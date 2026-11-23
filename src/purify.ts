/* eslint-disable @typescript-eslint/indent */

import type {
  TrustedHTML,
  TrustedTypesWindow,
} from 'trusted-types/lib/index.js';
import type { Config, UseProfilesConfig } from './config';
import * as TAGS from './tags.js';
import * as ATTRS from './attrs.js';
import * as EXPRESSIONS from './regexp.js';
import {
  addToSet,
  clone,
  entries,
  freeze,
  seal,
  arrayForEach,
  arrayLastIndexOf,
  arrayPop,
  arrayPush,
  arraySplice,
  stringMatch,
  stringReplace,
  stringToLowerCase,
  stringToString,
  stringIndexOf,
  stringTrim,
  regExpTest,
  typeErrorCreate,
  lookupAccessor,
  lookupGetter,
  create,
  objectHasOwnProperty,
} from './utils.js';

export type { Config } from './config';

declare const VERSION: string;

// https://developer.mozilla.org/en-US/docs/Web/API/Node/nodeType
const NODE_TYPE = {
  element: 1,
  attribute: 2,
  text: 3,
  cdataSection: 4,
  entityReference: 5, // Deprecated
  entityNode: 6, // Deprecated
  progressingInstruction: 7,
  comment: 8,
  document: 9,
  documentType: 10,
  documentFragment: 11,
  notation: 12, // Deprecated
};

/* HTML-namespace elements whose child text nodes are serialized *literally*
   (unescaped) by the HTML fragment-serialization algorithm. Two reparse-mXSS
   shapes ride on that literal serialization:
     (a) an element child - a tree the HTML parser can never build, but the DOM
         API and an XML/XHTML parse can - after which a `</tag>`-bearing text
         sibling breaks the element open on reparse; and
     (b) text-only content that already carries the element's OWN end tag, e.g.
         `<style>...</style><img onerror=x>` built as a node, which the literal
         serializer emits verbatim for the HTML parser to re-open.
   Shape (a) is handled by the firstElementChild branch in _isUnsafeNode; shape
   (b) by the LITERAL_TEXT_CLOSE probe. Both read textContent (the raw-serialized
   form for these elements) rather than innerHTML, because an XML/XHTML working
   document serializes innerHTML with `<` escaped, which silently blinds the
   innerHTML-based probes (rule 1's second probe and FALLBACK_TAG_CLOSE) there.
   `script` is never allow-listed, but is kept here so the guard matches the
   serializer's own literal-text list exactly. */
const LITERAL_TEXT_ELEMENT_NAMES = [
  'style',
  'script',
  'xmp',
  'iframe',
  'noembed',
  'noframes',
  'plaintext',
  'noscript',
];
const LITERAL_TEXT_ELEMENTS = freeze(addToSet({}, LITERAL_TEXT_ELEMENT_NAMES));

/* Per-element end-tag matcher. On an HTML reparse the ONLY token that
   terminates a literal-text element's raw content is its own end tag; a foreign
   literal-text close (e.g. `</xmp>` sitting inside `<style>`) does not break
   out, so matching is per-element, not a shared alternation. The lookahead
   requires an HTML tag-name terminator (whitespace, `/` or `>`) so a longer
   name such as `</styles` is not mistaken for `</style`. */
const LITERAL_TEXT_CLOSE = (function (): Record<string, RegExp> {
  const map: Record<string, RegExp> = {};
  arrayForEach(LITERAL_TEXT_ELEMENT_NAMES, (name) => {
    map[name] = seal(new RegExp('</' + name + '(?=[\\t\\n\\f\\r />])', 'i'));
  });
  return freeze(map);
})();

const getGlobal = function (): WindowLike {
  return typeof window === 'undefined' ? null : window;
};

/**
 * Creates a no-op policy for internal use only.
 * Don't export this function outside this module!
 * @param trustedTypes The policy factory.
 * @param purifyHostElement The Script element used to load DOMPurify (to determine policy name suffix).
 * @return The policy created (or null, if Trusted Types
 * are not supported or creating the policy failed).
 */
const _createTrustedTypesPolicy = function (
  trustedTypes: TrustedTypePolicyFactory,
  purifyHostElement: HTMLScriptElement
) {
  if (
    typeof trustedTypes !== 'object' ||
    typeof trustedTypes.createPolicy !== 'function'
  ) {
    return null;
  }

  // Allow the callers to control the unique policy name
  // by adding a data-tt-policy-suffix to the script element with the DOMPurify.
  // Policy creation with duplicate names throws in Trusted Types.
  let suffix = null;
  const ATTR_NAME = 'data-tt-policy-suffix';
  if (purifyHostElement && purifyHostElement.hasAttribute(ATTR_NAME)) {
    suffix = purifyHostElement.getAttribute(ATTR_NAME);
  }

  const policyName = 'dompurify' + (suffix ? '#' + suffix : '');

  try {
    return trustedTypes.createPolicy(policyName, {
      createHTML(html) {
        return html;
      },
      createScriptURL(scriptUrl) {
        return scriptUrl;
      },
    });
  } catch (_) {
    // Policy creation failed (most likely another DOMPurify script has
    // already run). Skip creating the policy, as this will only cause errors
    // if TT are enforced.
    console.warn(
      'TrustedTypes policy ' + policyName + ' could not be created.'
    );
    return null;
  }
};

const _createHooksMap = function (): HooksMap {
  return {
    afterSanitizeAttributes: [],
    afterSanitizeElements: [],
    afterSanitizeShadowDOM: [],
    beforeSanitizeAttributes: [],
    beforeSanitizeElements: [],
    beforeSanitizeShadowDOM: [],
    uponSanitizeAttribute: [],
    uponSanitizeElement: [],
    uponSanitizeShadowNode: [],
  };
};

function createDOMPurify(window: WindowLike = getGlobal()): DOMPurify {
  const DOMPurify: DOMPurify = (root: WindowLike) => createDOMPurify(root);

  DOMPurify.version = VERSION;

  DOMPurify.removed = [];

  if (
    !window ||
    !window.document ||
    window.document.nodeType !== NODE_TYPE.document ||
    !window.Element
  ) {
    // Not running in a browser, provide a factory function
    // so that you can pass your own Window
    DOMPurify.isSupported = false;

    return DOMPurify;
  }

  let { document } = window;

  const originalDocument = document;
  const currentScript: HTMLScriptElement =
    originalDocument.currentScript as HTMLScriptElement;
  const {
    DocumentFragment,
    HTMLTemplateElement,
    Node,
    Element,
    NodeFilter,
    NamedNodeMap = window.NamedNodeMap || (window as any).MozNamedAttrMap,
    HTMLFormElement,
    DOMParser,
    trustedTypes,
  } = window;

  const ElementPrototype = Element.prototype;

  const cloneNode = lookupGetter(ElementPrototype, 'cloneNode');
  const remove = lookupGetter(ElementPrototype, 'remove');
  const getNextSibling = lookupGetter(ElementPrototype, 'nextSibling');
  const getChildNodes = lookupGetter(ElementPrototype, 'childNodes');
  const getParentNode = lookupGetter(ElementPrototype, 'parentNode');
  const getAttributes = lookupGetter(ElementPrototype, 'attributes');
  const getNodeType =
    Node && Node.prototype ? lookupGetter(Node.prototype, 'nodeType') : null;
  const getNodeName =
    Node && Node.prototype ? lookupGetter(Node.prototype, 'nodeName') : null;
  const getOwnerDocument =
    Node && Node.prototype
      ? lookupGetter(Node.prototype, 'ownerDocument')
      : null;

  /* Element namespace through the cached Element.prototype getter, so a live
     node's own-property override cannot steer namespace decisions. */
  const getNamespaceURI = lookupAccessor(ElementPrototype, 'namespaceURI');
  const _readNamespaceURI = function (element: Element): string | null {
    return getNamespaceURI
      ? getNamespaceURI(element)
      : (element as any).namespaceURI;
  };

  // As per issue #47, the web-components registry is inherited by a
  // new document created via createHTMLDocument. As per the spec
  // (http://w3c.github.io/webcomponents/spec/custom/#creating-and-passing-registries)
  // a new empty registry is used when creating a template contents owner
  // document, so we use that as our parent document to ensure nothing
  // is inherited.
  if (typeof HTMLTemplateElement === 'function') {
    const template = document.createElement('template');
    if (template.content && template.content.ownerDocument) {
      document = template.content.ownerDocument;
    }
  }

  let trustedTypesPolicy;
  let emptyHTML = '';

  // The instance's own Trusted Types policy: created at most once (duplicate
  // policy names throw) and the only policy that survives clearConfig().
  let defaultTrustedTypesPolicy;
  let defaultTrustedTypesPolicyResolved = false;

  // A policy callback (createHTML or createScriptURL) that calls
  // DOMPurify.sanitize would recurse until the stack overflows (#1422); this
  // re-entry guard, shared by both callbacks, throws a clear error instead.
  let IN_TRUSTED_TYPES_POLICY = 0;
  const _assertNotInTrustedTypesPolicy = function (): void {
    if (IN_TRUSTED_TYPES_POLICY > 0) {
      throw typeErrorCreate(
        'A configured TRUSTED_TYPES_POLICY callback (createHTML or ' +
          'createScriptURL) must not call DOMPurify.sanitize, as that causes ' +
          'infinite recursion. Do not pass a policy whose callbacks wrap ' +
          'DOMPurify as TRUSTED_TYPES_POLICY; see the "DOMPurify and Trusted ' +
          'Types" section of the README.'
      );
    }
  };

  const _createTrustedHTML = function (html: string): string {
    _assertNotInTrustedTypesPolicy();

    IN_TRUSTED_TYPES_POLICY++;
    try {
      return trustedTypesPolicy.createHTML(html);
    } finally {
      IN_TRUSTED_TYPES_POLICY--;
    }
  };

  const _createTrustedScriptURL = function (scriptUrl: string): string {
    _assertNotInTrustedTypesPolicy();

    IN_TRUSTED_TYPES_POLICY++;
    try {
      return trustedTypesPolicy.createScriptURL(scriptUrl);
    } finally {
      IN_TRUSTED_TYPES_POLICY--;
    }
  };

  // Resolved at most once: createPolicy throws on a duplicate name, and a
  // failed or unsupported attempt must not be retried on every parse.
  const _getDefaultTrustedTypesPolicy = function () {
    if (!defaultTrustedTypesPolicyResolved) {
      defaultTrustedTypesPolicy = _createTrustedTypesPolicy(
        trustedTypes,
        currentScript
      );
      defaultTrustedTypesPolicyResolved = true;
    }

    return defaultTrustedTypesPolicy;
  };

  const {
    implementation,
    createNodeIterator,
    createDocumentFragment,
    getElementsByTagName,
  } = document;
  const { importNode } = originalDocument;

  let hooks = _createHooksMap();

  /**
   * Expose whether this browser supports running the full DOMPurify.
   */
  DOMPurify.isSupported =
    typeof entries === 'function' &&
    typeof getParentNode === 'function' &&
    implementation &&
    implementation.createHTMLDocument !== undefined;

  const {
    MUSTACHE_EXPR,
    ERB_EXPR,
    TMPLIT_EXPR,
    DATA_ATTR,
    ARIA_ATTR,
    IS_SCRIPT_OR_DATA,
    ATTR_WHITESPACE,
    CUSTOM_ELEMENT,
  } = EXPRESSIONS;

  let { IS_ALLOWED_URI } = EXPRESSIONS;

  /**
   * We consider the elements and attributes below to be safe. Ideally
   * don't add any new ones but feel free to remove unwanted ones.
   */

  /* allowed element names */
  let ALLOWED_TAGS = null;
  const DEFAULT_ALLOWED_TAGS = addToSet({}, [
    ...TAGS.html,
    ...TAGS.svg,
    ...TAGS.svgFilters,
    ...TAGS.mathMl,
    ...TAGS.text,
  ]);

  /* Allowed attribute names */
  let ALLOWED_ATTR = null;
  const DEFAULT_ALLOWED_ATTR = addToSet({}, [
    ...ATTRS.html,
    ...ATTRS.svg,
    ...ATTRS.mathMl,
    ...ATTRS.xml,
  ]);

  /*
   * Configure how DOMPurify should handle custom elements and their attributes as well as customized built-in elements.
   * @property {RegExp|Function|null} tagNameCheck one of [null, regexPattern, predicate]. Default: `null` (disallow any custom elements)
   * @property {RegExp|Function|null} attributeNameCheck one of [null, regexPattern, predicate]. Default: `null` (disallow any attributes not on the allow list)
   * @property {boolean} allowCustomizedBuiltInElements allow custom elements derived from built-ins if they pass CUSTOM_ELEMENT_HANDLING.tagNameCheck. Default: `false`.
   */
  let CUSTOM_ELEMENT_HANDLING = Object.seal(
    create(null, {
      tagNameCheck: {
        writable: true,
        configurable: false,
        enumerable: true,
        value: null,
      },
      attributeNameCheck: {
        writable: true,
        configurable: false,
        enumerable: true,
        value: null,
      },
      allowCustomizedBuiltInElements: {
        writable: true,
        configurable: false,
        enumerable: true,
        value: false,
      },
    })
  );

  /* Explicitly forbidden tags (overrides ALLOWED_TAGS/ADD_TAGS) */
  let FORBID_TAGS = null;

  /* Explicitly forbidden attributes (overrides ALLOWED_ATTR/ADD_ATTR) */
  let FORBID_ATTR = null;

  /* Config object to store ADD_TAGS/ADD_ATTR functions (when used as functions) */
  const EXTRA_ELEMENT_HANDLING = Object.seal(
    create(null, {
      tagCheck: {
        writable: true,
        configurable: false,
        enumerable: true,
        value: null,
      },
      attributeCheck: {
        writable: true,
        configurable: false,
        enumerable: true,
        value: null,
      },
    })
  );

  /* Decide if ARIA attributes are okay */
  let ALLOW_ARIA_ATTR = true;

  /* Decide if custom data attributes are okay */
  let ALLOW_DATA_ATTR = true;

  /* Decide if unknown protocols are okay */
  let ALLOW_UNKNOWN_PROTOCOLS = false;

  /* Decide if self-closing tags in attributes are allowed.
   * Usually removed due to a mXSS issue in jQuery 3.0 */
  let ALLOW_SELF_CLOSE_IN_ATTR = true;

  /* Output should be safe for common template engines.
   * This means, DOMPurify removes data attributes, mustaches and ERB
   */
  let SAFE_FOR_TEMPLATES = false;

  /* Output should be safe even for XML used within HTML and alike.
   * This means, DOMPurify removes comments when containing risky content.
   */
  let SAFE_FOR_XML = true;

  /* Decide if document with <html>... should be returned */
  let WHOLE_DOCUMENT = false;

  /* Track whether config is already set on this instance of DOMPurify. */
  let SET_CONFIG = false;

  /* Pristine allowlist bindings captured at setConfig() time. On the
   * persistent-config path sanitize() restores the sets from these before
   * the per-walk hook clone-guard, so a hook's in-call widening cannot
   * carry across calls. Null until setConfig() is called; reset by
   * clearConfig(). */
  let SET_CONFIG_ALLOWED_TAGS = null;
  let SET_CONFIG_ALLOWED_ATTR = null;

  /* Decide if all elements (e.g. style, script) must be children of
   * document.body. By default, browsers might move them to document.head */
  let FORCE_BODY = false;

  /* Decide if a DOM `HTMLBodyElement` should be returned, instead of a html
   * string (or a TrustedHTML object if Trusted Types are supported).
   * If `WHOLE_DOCUMENT` is enabled a `HTMLHtmlElement` will be returned instead
   */
  let RETURN_DOM = false;

  /* Decide if a DOM `DocumentFragment` should be returned, instead of a html
   * string  (or a TrustedHTML object if Trusted Types are supported) */
  let RETURN_DOM_FRAGMENT = false;

  /* Try to return a Trusted Type object instead of a string, return a string in
   * case Trusted Types are not supported  */
  let RETURN_TRUSTED_TYPE = false;

  /* Output should be free from DOM clobbering attacks?
   * This sanitizes markups named with colliding, clobberable built-in DOM APIs.
   */
  let SANITIZE_DOM = true;

  /* Achieve full DOM Clobbering protection by isolating the namespace of named
   * properties and JS variables, mitigating attacks that abuse the HTML/DOM spec rules.
   *
   * HTML/DOM spec rules that enable DOM Clobbering:
   *   - Named Access on Window (§7.3.3)
   *   - DOM Tree Accessors (§3.1.5)
   *   - Form Element Parent-Child Relations (§4.10.3)
   *   - Iframe srcdoc / Nested WindowProxies (§4.8.5)
   *   - HTMLCollection (§4.2.10.2)
   *
   * Namespace isolation is implemented by prefixing `id` and `name` attributes
   * with a constant string, i.e., `user-content-`
   */
  let SANITIZE_NAMED_PROPS = false;
  const SANITIZE_NAMED_PROPS_PREFIX = 'user-content-';

  /* Keep element content when removing element? */
  let KEEP_CONTENT = true;

  /* If a `Node` is passed to sanitize(), then performs sanitization in-place instead
   * of importing it into a new Document and returning a sanitized copy */
  let IN_PLACE = false;

  /* Allow usage of profiles like html, svg and mathMl */
  let USE_PROFILES: UseProfilesConfig | false = {};

  /* Tags to ignore content of when KEEP_CONTENT is true */
  let FORBID_CONTENTS = null;
  const DEFAULT_FORBID_CONTENTS = addToSet({}, [
    'annotation-xml',
    'audio',
    'colgroup',
    'desc',
    'foreignobject',
    'head',
    'iframe',
    'math',
    'mi',
    'mn',
    'mo',
    'ms',
    'mtext',
    'noembed',
    'noframes',
    'noscript',
    'plaintext',
    'script',
    'style',
    'svg',
    'template',
    'thead',
    'title',
    'video',
    'xmp',
  ]);

  /* Tags that are safe for data: URIs */
  let DATA_URI_TAGS = null;
  const DEFAULT_DATA_URI_TAGS = addToSet({}, [
    'audio',
    'video',
    'img',
    'source',
    'image',
    'track',
  ]);

  /* Attributes safe for values like "javascript:" */
  let URI_SAFE_ATTRIBUTES = null;
  const DEFAULT_URI_SAFE_ATTRIBUTES = addToSet({}, [
    'alt',
    'class',
    'for',
    'id',
    'label',
    'name',
    'pattern',
    'placeholder',
    'role',
    'summary',
    'title',
    'value',
    'style',
    'xmlns',
  ]);

  const MATHML_NAMESPACE = 'http://www.w3.org/1998/Math/MathML';
  const SVG_NAMESPACE = 'http://www.w3.org/2000/svg';
  const HTML_NAMESPACE = 'http://www.w3.org/1999/xhtml';
  /* Document namespace */
  let NAMESPACE = HTML_NAMESPACE;
  let IS_EMPTY_INPUT = false;

  /* Allowed XHTML+XML namespaces */
  let ALLOWED_NAMESPACES = null;
  const DEFAULT_ALLOWED_NAMESPACES = addToSet(
    {},
    [MATHML_NAMESPACE, SVG_NAMESPACE, HTML_NAMESPACE],
    stringToString
  );

  let MATHML_TEXT_INTEGRATION_POINTS = addToSet({}, [
    'mi',
    'mo',
    'mn',
    'ms',
    'mtext',
  ]);

  let HTML_INTEGRATION_POINTS = addToSet({}, ['annotation-xml']);

  // Certain elements are allowed in both SVG and HTML
  // namespace. We need to specify them explicitly
  // so that they don't get erroneously deleted from
  // HTML namespace.
  const COMMON_SVG_AND_HTML_ELEMENTS = addToSet({}, [
    'title',
    'style',
    'font',
    'a',
    'script',
  ]);

  /* Parsing of strict XHTML documents */
  let PARSER_MEDIA_TYPE: null | DOMParserSupportedType = null;
  const SUPPORTED_PARSER_MEDIA_TYPES = ['application/xhtml+xml', 'text/html'];
  const DEFAULT_PARSER_MEDIA_TYPE = 'text/html';
  let transformCaseFunc: null | Parameters<typeof addToSet>[2] = null;

  /* Keep a reference to config to pass to hooks */
  let CONFIG: Config | null = null;

  /* Ideally, do not touch anything below this line */
  /* ______________________________________________ */

  const formElement = document.createElement('form');

  const isRegexOrFunction = function (
    testValue: unknown
  ): testValue is Function | RegExp {
    return testValue instanceof RegExp || testValue instanceof Function;
  };

  /**
   * _parseConfig
   *
   * @param cfg optional config literal
   */
  // eslint-disable-next-line complexity
  const _parseConfig = function (cfg: Config = {}): void {
    if (CONFIG && CONFIG === cfg) {
      return;
    }

    /* Shield configuration object from tampering */
    if (!cfg || typeof cfg !== 'object') {
      cfg = {};
    }

    /* Shield configuration object from prototype pollution */
    cfg = clone(cfg);

    PARSER_MEDIA_TYPE =
      // eslint-disable-next-line unicorn/prefer-includes
      SUPPORTED_PARSER_MEDIA_TYPES.indexOf(cfg.PARSER_MEDIA_TYPE) === -1
        ? DEFAULT_PARSER_MEDIA_TYPE
        : cfg.PARSER_MEDIA_TYPE;

    // HTML tags and attributes are not case-sensitive, converting to lowercase. Keeping XHTML as is.
    transformCaseFunc =
      PARSER_MEDIA_TYPE === 'application/xhtml+xml'
        ? stringToString
        : stringToLowerCase;

    /* Set configuration parameters */
    ALLOWED_TAGS = objectHasOwnProperty(cfg, 'ALLOWED_TAGS')
      ? addToSet({}, cfg.ALLOWED_TAGS, transformCaseFunc)
      : DEFAULT_ALLOWED_TAGS;
    ALLOWED_ATTR = objectHasOwnProperty(cfg, 'ALLOWED_ATTR')
      ? addToSet({}, cfg.ALLOWED_ATTR, transformCaseFunc)
      : DEFAULT_ALLOWED_ATTR;
    ALLOWED_NAMESPACES = objectHasOwnProperty(cfg, 'ALLOWED_NAMESPACES')
      ? addToSet({}, cfg.ALLOWED_NAMESPACES, stringToString)
      : DEFAULT_ALLOWED_NAMESPACES;
    URI_SAFE_ATTRIBUTES = objectHasOwnProperty(cfg, 'ADD_URI_SAFE_ATTR')
      ? addToSet(
          clone(DEFAULT_URI_SAFE_ATTRIBUTES),
          cfg.ADD_URI_SAFE_ATTR,
          transformCaseFunc
        )
      : DEFAULT_URI_SAFE_ATTRIBUTES;
    DATA_URI_TAGS = objectHasOwnProperty(cfg, 'ADD_DATA_URI_TAGS')
      ? addToSet(
          clone(DEFAULT_DATA_URI_TAGS),
          cfg.ADD_DATA_URI_TAGS,
          transformCaseFunc
        )
      : DEFAULT_DATA_URI_TAGS;
    FORBID_CONTENTS = objectHasOwnProperty(cfg, 'FORBID_CONTENTS')
      ? addToSet({}, cfg.FORBID_CONTENTS, transformCaseFunc)
      : DEFAULT_FORBID_CONTENTS;
    FORBID_TAGS = objectHasOwnProperty(cfg, 'FORBID_TAGS')
      ? addToSet({}, cfg.FORBID_TAGS, transformCaseFunc)
      : clone({});
    FORBID_ATTR = objectHasOwnProperty(cfg, 'FORBID_ATTR')
      ? addToSet({}, cfg.FORBID_ATTR, transformCaseFunc)
      : clone({});
    USE_PROFILES = objectHasOwnProperty(cfg, 'USE_PROFILES')
      ? cfg.USE_PROFILES
      : false;
    ALLOW_ARIA_ATTR = cfg.ALLOW_ARIA_ATTR !== false; // Default true
    ALLOW_DATA_ATTR = cfg.ALLOW_DATA_ATTR !== false; // Default true
    ALLOW_UNKNOWN_PROTOCOLS = cfg.ALLOW_UNKNOWN_PROTOCOLS || false; // Default false
    ALLOW_SELF_CLOSE_IN_ATTR = cfg.ALLOW_SELF_CLOSE_IN_ATTR !== false; // Default true
    SAFE_FOR_TEMPLATES = cfg.SAFE_FOR_TEMPLATES || false; // Default false
    SAFE_FOR_XML = cfg.SAFE_FOR_XML !== false; // Default true
    WHOLE_DOCUMENT = cfg.WHOLE_DOCUMENT || false; // Default false
    RETURN_DOM = cfg.RETURN_DOM || false; // Default false
    RETURN_DOM_FRAGMENT = cfg.RETURN_DOM_FRAGMENT || false; // Default false
    RETURN_TRUSTED_TYPE = cfg.RETURN_TRUSTED_TYPE || false; // Default false
    FORCE_BODY = cfg.FORCE_BODY || false; // Default false
    SANITIZE_DOM = cfg.SANITIZE_DOM !== false; // Default true
    SANITIZE_NAMED_PROPS = cfg.SANITIZE_NAMED_PROPS || false; // Default false
    KEEP_CONTENT = cfg.KEEP_CONTENT !== false; // Default true
    IN_PLACE = cfg.IN_PLACE || false; // Default false
    IS_ALLOWED_URI = cfg.ALLOWED_URI_REGEXP || EXPRESSIONS.IS_ALLOWED_URI;
    NAMESPACE = cfg.NAMESPACE || HTML_NAMESPACE;
    MATHML_TEXT_INTEGRATION_POINTS =
      cfg.MATHML_TEXT_INTEGRATION_POINTS || MATHML_TEXT_INTEGRATION_POINTS;
    HTML_INTEGRATION_POINTS =
      cfg.HTML_INTEGRATION_POINTS || HTML_INTEGRATION_POINTS;

    CUSTOM_ELEMENT_HANDLING = cfg.CUSTOM_ELEMENT_HANDLING || create(null);
    if (
      cfg.CUSTOM_ELEMENT_HANDLING &&
      isRegexOrFunction(cfg.CUSTOM_ELEMENT_HANDLING.tagNameCheck)
    ) {
      CUSTOM_ELEMENT_HANDLING.tagNameCheck =
        cfg.CUSTOM_ELEMENT_HANDLING.tagNameCheck;
    }

    if (
      cfg.CUSTOM_ELEMENT_HANDLING &&
      isRegexOrFunction(cfg.CUSTOM_ELEMENT_HANDLING.attributeNameCheck)
    ) {
      CUSTOM_ELEMENT_HANDLING.attributeNameCheck =
        cfg.CUSTOM_ELEMENT_HANDLING.attributeNameCheck;
    }

    if (
      cfg.CUSTOM_ELEMENT_HANDLING &&
      typeof cfg.CUSTOM_ELEMENT_HANDLING.allowCustomizedBuiltInElements ===
        'boolean'
    ) {
      CUSTOM_ELEMENT_HANDLING.allowCustomizedBuiltInElements =
        cfg.CUSTOM_ELEMENT_HANDLING.allowCustomizedBuiltInElements;
    }

    if (SAFE_FOR_TEMPLATES) {
      ALLOW_DATA_ATTR = false;
    }

    if (RETURN_DOM_FRAGMENT) {
      RETURN_DOM = true;
    }

    /* Parse profile info */
    if (USE_PROFILES) {
      ALLOWED_TAGS = addToSet({}, TAGS.text);
      ALLOWED_ATTR = create(null);
      if (USE_PROFILES.html === true) {
        addToSet(ALLOWED_TAGS, TAGS.html);
        addToSet(ALLOWED_ATTR, ATTRS.html);
      }

      if (USE_PROFILES.svg === true) {
        addToSet(ALLOWED_TAGS, TAGS.svg);
        addToSet(ALLOWED_ATTR, ATTRS.svg);
        addToSet(ALLOWED_ATTR, ATTRS.xml);
      }

      if (USE_PROFILES.svgFilters === true) {
        addToSet(ALLOWED_TAGS, TAGS.svgFilters);
        addToSet(ALLOWED_ATTR, ATTRS.svg);
        addToSet(ALLOWED_ATTR, ATTRS.xml);
      }

      if (USE_PROFILES.mathMl === true) {
        addToSet(ALLOWED_TAGS, TAGS.mathMl);
        addToSet(ALLOWED_ATTR, ATTRS.mathMl);
        addToSet(ALLOWED_ATTR, ATTRS.xml);
      }
    }

    /* Prevent function-based ADD_ATTR / ADD_TAGS from leaking across calls */
    if (!objectHasOwnProperty(cfg, 'ADD_TAGS')) {
      EXTRA_ELEMENT_HANDLING.tagCheck = null;
    }

    if (!objectHasOwnProperty(cfg, 'ADD_ATTR')) {
      EXTRA_ELEMENT_HANDLING.attributeCheck = null;
    }

    /* Merge configuration parameters */
    if (cfg.ADD_TAGS) {
      if (typeof cfg.ADD_TAGS === 'function') {
        EXTRA_ELEMENT_HANDLING.tagCheck = cfg.ADD_TAGS;
      } else {
        if (ALLOWED_TAGS === DEFAULT_ALLOWED_TAGS) {
          ALLOWED_TAGS = clone(ALLOWED_TAGS);
        }

        addToSet(ALLOWED_TAGS, cfg.ADD_TAGS, transformCaseFunc);
      }
    }

    if (cfg.ADD_ATTR) {
      if (typeof cfg.ADD_ATTR === 'function') {
        EXTRA_ELEMENT_HANDLING.attributeCheck = cfg.ADD_ATTR;
      } else {
        if (ALLOWED_ATTR === DEFAULT_ALLOWED_ATTR) {
          ALLOWED_ATTR = clone(ALLOWED_ATTR);
        }

        addToSet(ALLOWED_ATTR, cfg.ADD_ATTR, transformCaseFunc);
      }
    }

    if (cfg.ADD_URI_SAFE_ATTR) {
      addToSet(URI_SAFE_ATTRIBUTES, cfg.ADD_URI_SAFE_ATTR, transformCaseFunc);
    }

    if (cfg.FORBID_CONTENTS) {
      if (FORBID_CONTENTS === DEFAULT_FORBID_CONTENTS) {
        FORBID_CONTENTS = clone(FORBID_CONTENTS);
      }

      addToSet(FORBID_CONTENTS, cfg.FORBID_CONTENTS, transformCaseFunc);
    }

    if (cfg.ADD_FORBID_CONTENTS) {
      if (FORBID_CONTENTS === DEFAULT_FORBID_CONTENTS) {
        FORBID_CONTENTS = clone(FORBID_CONTENTS);
      }

      addToSet(FORBID_CONTENTS, cfg.ADD_FORBID_CONTENTS, transformCaseFunc);
    }

    /* Add #text in case KEEP_CONTENT is set to true */
    if (KEEP_CONTENT) {
      ALLOWED_TAGS['#text'] = true;
    }

    /* Add html, head and body to ALLOWED_TAGS in case WHOLE_DOCUMENT is true */
    if (WHOLE_DOCUMENT) {
      addToSet(ALLOWED_TAGS, ['html', 'head', 'body']);
    }

    /* Add tbody to ALLOWED_TAGS in case tables are permitted, see #286, #365 */
    if (ALLOWED_TAGS.table) {
      addToSet(ALLOWED_TAGS, ['tbody']);
      delete FORBID_TAGS.tbody;
    }

    // A caller policy must not outlive clearConfig() or TRUSTED_TYPES_POLICY:
    // null, or it signs later RETURN_TRUSTED_TYPE output. GHSA-vxr8-fq34-vvx9.
    if (cfg.TRUSTED_TYPES_POLICY) {
      if (typeof cfg.TRUSTED_TYPES_POLICY.createHTML !== 'function') {
        throw typeErrorCreate(
          'TRUSTED_TYPES_POLICY configuration option must provide a "createHTML" hook.'
        );
      }

      if (typeof cfg.TRUSTED_TYPES_POLICY.createScriptURL !== 'function') {
        throw typeErrorCreate(
          'TRUSTED_TYPES_POLICY configuration option must provide a "createScriptURL" hook.'
        );
      }

      // A caller-supplied policy applies to this configuration only.
      const previousTrustedTypesPolicy = trustedTypesPolicy;
      trustedTypesPolicy = cfg.TRUSTED_TYPES_POLICY;

      // Sign local variables required by `sanitize`. A circular policy throws
      // via the re-entry guard; restore the previous one so the instance is not
      // left poisoned. See #1422.
      try {
        emptyHTML = _createTrustedHTML('');
      } catch (error) {
        trustedTypesPolicy = previousTrustedTypesPolicy;
        throw error;
      }
    } else if (cfg.TRUSTED_TYPES_POLICY === null) {
      // Opt-out for this call: no signing, nothing created (#1422). undefined,
      // not null, drops a retained caller policy and lets the next config-less
      // call restore the internal one. See GHSA-vxr8-fq34-vvx9.
      trustedTypesPolicy = undefined;
      emptyHTML = '';
    } else {
      // A previously supplied policy stays active across config-less calls on
      // purpose; only clearConfig() or null drops it.
      if (trustedTypesPolicy === undefined) {
        trustedTypesPolicy = _getDefaultTrustedTypesPolicy();
      }

      // Sign internal variables only when a policy is active, so `.createHTML`
      // is never called on a non-policy. See #1422.
      if (trustedTypesPolicy && typeof emptyHTML === 'string') {
        emptyHTML = _createTrustedHTML('');
      }
    }

    /*
     * Mirror the clone-before-mutate pattern already applied above for
     * cfg.ADD_TAGS / cfg.ADD_ATTR: if any uponSanitize* hook is
     * registered AND the set still points at the default constant,
     * clone it. The hook then mutates the clone (in-call widening
     * still works exactly as documented) and the next default-cfg
     * call rebinds to the untouched original via the reassignment at
     * the top of this function.
     */
    if (
      (hooks.uponSanitizeElement.length > 0 ||
        hooks.uponSanitizeAttribute.length > 0) &&
      ALLOWED_TAGS === DEFAULT_ALLOWED_TAGS
    ) {
      ALLOWED_TAGS = clone(ALLOWED_TAGS);
    }

    if (
      hooks.uponSanitizeAttribute.length > 0 &&
      ALLOWED_ATTR === DEFAULT_ALLOWED_ATTR
    ) {
      ALLOWED_ATTR = clone(ALLOWED_ATTR);
    }

    // Prevent further manipulation of configuration.
    // Not available in IE8, Safari 5, etc.
    if (freeze) {
      freeze(cfg);
    }

    CONFIG = cfg;
  };

  /* Keep track of all possible SVG and MathML tags
   * so that we can perform the namespace checks
   * correctly. */
  const ALL_SVG_TAGS = addToSet({}, [
    ...TAGS.svg,
    ...TAGS.svgFilters,
    ...TAGS.svgDisallowed,
  ]);
  const ALL_MATHML_TAGS = addToSet({}, [
    ...TAGS.mathMl,
    ...TAGS.mathMlDisallowed,
  ]);

  /**
   * @param element a DOM element whose namespace is being checked
   * @returns Return false if the element has a
   *  namespace that a spec-compliant parser would never
   *  return. Return true otherwise.
   */
  const _checkValidNamespace = function (element: Element): boolean {
    /* Names and namespaces come from the cached prototype getters: own-property
       tagName / namespaceURI overrides on a live IN_PLACE node must not steer
       this (same root cause as GHSA-x4vx-rjvf-j5p4). */
    const elementNamespace = _readNamespaceURI(element);
    const tagName = stringToLowerCase(
      getNodeName ? getNodeName(element) : element.nodeName
    );

    // A missing parent (JSDOM inside shadow DOM) or a non-element parent
    // is simulated as a <template> in the configured namespace.
    const parentNode = getParentNode(element);
    let parent: { namespaceURI: string | null };
    let parentTagName: string;
    if (
      parentNode &&
      (getNodeType ? getNodeType(parentNode) : parentNode.nodeType) ===
        NODE_TYPE.element
    ) {
      parent = { namespaceURI: _readNamespaceURI(parentNode) };
      parentTagName = stringToLowerCase(
        getNodeName ? getNodeName(parentNode) : parentNode.nodeName
      );
    } else {
      parent = { namespaceURI: NAMESPACE };
      parentTagName = 'template';
    }

    if (!ALLOWED_NAMESPACES[elementNamespace]) {
      return false;
    }

    if (elementNamespace === SVG_NAMESPACE) {
      // The only way to switch from HTML namespace to SVG
      // is via <svg>. If it happens via any other tag, then
      // it should be killed.
      if (parent.namespaceURI === HTML_NAMESPACE) {
        return tagName === 'svg';
      }

      // The only way to switch from MathML to SVG is via`
      // svg if parent is either <annotation-xml> or MathML
      // text integration points.
      if (parent.namespaceURI === MATHML_NAMESPACE) {
        return (
          tagName === 'svg' &&
          (parentTagName === 'annotation-xml' ||
            MATHML_TEXT_INTEGRATION_POINTS[parentTagName])
        );
      }

      // We only allow elements that are defined in SVG
      // spec. All others are disallowed in SVG namespace.
      return Boolean(ALL_SVG_TAGS[tagName]);
    }

    if (elementNamespace === MATHML_NAMESPACE) {
      // The only way to switch from HTML namespace to MathML
      // is via <math>. If it happens via any other tag, then
      // it should be killed.
      if (parent.namespaceURI === HTML_NAMESPACE) {
        return tagName === 'math';
      }

      // The only way to switch from SVG to MathML is via
      // <math> and HTML integration points
      if (parent.namespaceURI === SVG_NAMESPACE) {
        return tagName === 'math' && HTML_INTEGRATION_POINTS[parentTagName];
      }

      // We only allow elements that are defined in MathML
      // spec. All others are disallowed in MathML namespace.
      return Boolean(ALL_MATHML_TAGS[tagName]);
    }

    if (elementNamespace === HTML_NAMESPACE) {
      // The only way to switch from SVG to HTML is via
      // HTML integration points, and from MathML to HTML
      // is via MathML text integration points
      if (
        parent.namespaceURI === SVG_NAMESPACE &&
        !HTML_INTEGRATION_POINTS[parentTagName]
      ) {
        return false;
      }

      if (
        parent.namespaceURI === MATHML_NAMESPACE &&
        !MATHML_TEXT_INTEGRATION_POINTS[parentTagName]
      ) {
        return false;
      }

      // We disallow tags that are specific for MathML
      // or SVG and should never appear in HTML namespace
      return (
        !ALL_MATHML_TAGS[tagName] &&
        (COMMON_SVG_AND_HTML_ELEMENTS[tagName] || !ALL_SVG_TAGS[tagName])
      );
    }

    // For XHTML and XML documents that support custom namespaces
    if (
      PARSER_MEDIA_TYPE === 'application/xhtml+xml' &&
      ALLOWED_NAMESPACES[elementNamespace]
    ) {
      return true;
    }

    // The code should never reach this place (this means
    // that the element somehow got namespace that is not
    // HTML, SVG, MathML or allowed via ALLOWED_NAMESPACES).
    // Return false just in case.
    return false;
  };

  /**
   * _forceRemove
   *
   * @param node a DOM node
   */
  const _forceRemove = function (node: Node): void {
    arrayPush(DOMPurify.removed, { element: node });

    try {
      // eslint-disable-next-line unicorn/prefer-dom-node-remove
      getParentNode(node).removeChild(node);
    } catch (_) {
      /* The remove() fallback is a no-op on a parentless node (an IN_PLACE
         root), which would come back intact: fail closed by throwing, never by
         neutralizing it via its clobberable methods. GHSA-r47g-fvhr-h676. */
      remove(node);

      if (!getParentNode(node)) {
        throw typeErrorCreate(
          'a node selected for removal could not be detached from its tree ' +
            'and cannot be safely returned; refusing to sanitize in place'
        );
      }
    }
  };

  /**
   * _removeAttribute
   *
   * @param name an Attribute name
   * @param element a DOM node
   */
  const _removeAttribute = function (name: string, element: Element): void {
    try {
      arrayPush(DOMPurify.removed, {
        attribute: element.getAttributeNode(name),
        from: element,
      });
    } catch (_) {
      arrayPush(DOMPurify.removed, {
        attribute: null,
        from: element,
      });
    }

    element.removeAttribute(name);

    // We void attribute values for unremovable "is" attributes
    if (name === 'is') {
      if (RETURN_DOM || RETURN_DOM_FRAGMENT) {
        try {
          _forceRemove(element);
        } catch (_) {}
      } else {
        try {
          element.setAttribute(name, '');
        } catch (_) {}
      }
    }
  };

  /**
   * _stripDisallowedAttributes
   *
   * Removes every attribute the active configuration does not allow from a
   * single element, using the same allowlist as the main attribute pass (so
   * `on*` handlers go, but no `/^on/` blocklist is introduced). Used only to
   * neutralise nodes that are being discarded from an in-place tree.
   *
   * @param element the element to strip
   */
  const _stripDisallowedAttributes = function (element: Element): void {
    const attributes = getAttributes
      ? getAttributes(element)
      : element.attributes;
    if (!attributes) {
      return;
    }

    for (let i = attributes.length - 1; i >= 0; --i) {
      const attribute = attributes[i];
      const name = attribute && attribute.name;
      if (typeof name !== 'string' || ALLOWED_ATTR[transformCaseFunc(name)]) {
        continue;
      }

      try {
        element.removeAttribute(name);
      } catch (_) {
        /* Clobbered removeAttribute on a doomed node — ignore */
      }
    }
  };

  /**
   * _neutralizeSubtree
   *
   * Strips every attribute the active configuration does not allow from a
   * subtree that leaves an IN_PLACE tree, so a queued resource handler on it
   * cannot fire after sanitize returns. Hook-free by design.
   *
   * @param root the root of a removed subtree to neutralise
   */
  const _neutralizeSubtree = function (root: Node): void {
    const stack: Node[] = [root];

    while (stack.length > 0) {
      const node = stack.pop();
      const nodeType = getNodeType ? getNodeType(node) : (node as any).nodeType;

      if (nodeType === NODE_TYPE.element) {
        _stripDisallowedAttributes(node as Element);
      }

      const childNodes = getChildNodes
        ? getChildNodes(node)
        : (node as Element).childNodes;
      if (childNodes) {
        for (let i = childNodes.length - 1; i >= 0; --i) {
          stack.push(childNodes[i]);
        }
      }
    }
  };

  /**
   * _initDocument
   *
   * @param dirty - a string of dirty markup
   * @return a DOM, filled with the dirty markup
   */
  const _initDocument = function (dirty: string): Document {
    /* Create a HTML document */
    let doc = null;
    let leadingWhitespace = null;

    if (FORCE_BODY) {
      dirty = '<remove></remove>' + dirty;
    } else {
      /* If FORCE_BODY isn't used, leading whitespace needs to be preserved manually */
      const matches = stringMatch(dirty, /^[\r\n\t ]+/);
      leadingWhitespace = matches && matches[0];
    }

    if (
      PARSER_MEDIA_TYPE === 'application/xhtml+xml' &&
      NAMESPACE === HTML_NAMESPACE
    ) {
      // Root of XHTML doc must contain xmlns declaration (see https://www.w3.org/TR/xhtml1/normative.html#strict)
      dirty =
        '<html xmlns="http://www.w3.org/1999/xhtml"><head></head><body>' +
        dirty +
        '</body></html>';
    }

    const dirtyPayload = trustedTypesPolicy ? _createTrustedHTML(dirty) : dirty;
    /*
     * Use the DOMParser API by default, fallback later if needs be
     * DOMParser not work for svg when has multiple root element.
     */
    if (NAMESPACE === HTML_NAMESPACE) {
      try {
        doc = new DOMParser().parseFromString(dirtyPayload, PARSER_MEDIA_TYPE);
      } catch (_) {}
    }

    /* Use createHTMLDocument in case DOMParser is not available */
    if (!doc || !doc.documentElement) {
      doc = implementation.createDocument(NAMESPACE, 'template', null);
      try {
        doc.documentElement.innerHTML = IS_EMPTY_INPUT
          ? emptyHTML
          : dirtyPayload;
      } catch (_) {
        // Syntax error if dirtyPayload is invalid xml
      }
    }

    const body = doc.body || doc.documentElement;

    if (dirty && leadingWhitespace) {
      body.insertBefore(
        document.createTextNode(leadingWhitespace),
        body.childNodes[0] || null
      );
    }

    /* Work on whole document or just its body */
    if (NAMESPACE === HTML_NAMESPACE) {
      return getElementsByTagName.call(
        doc,
        WHOLE_DOCUMENT ? 'html' : 'body'
      )[0];
    }

    return WHOLE_DOCUMENT ? doc.documentElement : body;
  };

  /**
   * Creates a NodeIterator object that you can use to traverse filtered lists of nodes or elements in a document.
   *
   * @param root The root element or node to start traversing on.
   * @return The created NodeIterator
   */
  const _createNodeIterator = function (root: Node): NodeIterator {
    /* Read ownerDocument through the cached Node.prototype getter, never the
       direct property. HTMLFormElement has [LegacyOverrideBuiltIns], so a
       clobbering child (<input name="ownerDocument"> or a form-associated
       external input) shadows the prototype getter and makes a direct read
       return that <input>. createNodeIterator.call(<input>, ...) then throws
       "Illegal invocation", and on the IN_PLACE path that throw lands before
       the walk's fail-closed barrier - leaving the caller's live tree, with
       any already-armed handler in it, un-neutralized. The cached getter
       returns the real Document regardless of the clobber. */
    const doc = getOwnerDocument ? getOwnerDocument(root) : root.ownerDocument;
    return createNodeIterator.call(
      doc || root,
      root,
      // eslint-disable-next-line no-bitwise
      NodeFilter.SHOW_ELEMENT |
        NodeFilter.SHOW_COMMENT |
        NodeFilter.SHOW_TEXT |
        NodeFilter.SHOW_PROCESSING_INSTRUCTION |
        NodeFilter.SHOW_CDATA_SECTION,
      null
    );
  };

  /**
   * Strip template-engine expressions ({{...}}, ${...}, <%...%>) from the
   * character data of an element subtree. Used as the final safety net for
   * SAFE_FOR_TEMPLATES on every DOM-returning code path so that expressions
   * which only form after text-node normalization (e.g. fragments split across
   * stripped elements) cannot survive into a template-evaluating framework.
   *
   * Walks text/comment/CDATA/processing-instruction nodes and mutates `.data`
   * in place rather than round-tripping through innerHTML. This preserves
   * descendant node references (important for IN_PLACE callers), avoids a
   * serialize/reparse cycle, and reads literal character data — which means
   * `<%...%>` in text content matches the ERB regex against its real bytes
   * instead of the HTML-entity-escaped form innerHTML would produce.
   *
   * Attribute values are not visited here; SAFE_FOR_TEMPLATES handling for
   * attributes is performed during the per-node `_sanitizeAttributes` pass.
   *
   * @param node The root element whose character data should be scrubbed.
   */
  const _scrubTemplateExpressions = function (node: Element): void {
    node.normalize();
    /* Clobber-safe ownerDocument read, same reasoning as _createNodeIterator:
       under SAFE_FOR_TEMPLATES this runs on the live IN_PLACE root, which may
       carry a form-named-getter override of ownerDocument. */
    const doc = getOwnerDocument ? getOwnerDocument(node) : node.ownerDocument;
    const walker = createNodeIterator.call(
      doc || node,
      node,
      // eslint-disable-next-line no-bitwise
      NodeFilter.SHOW_TEXT |
        NodeFilter.SHOW_COMMENT |
        NodeFilter.SHOW_CDATA_SECTION |
        NodeFilter.SHOW_PROCESSING_INSTRUCTION,
      null
    );

    let currentNode = walker.nextNode() as CharacterData | null;
    while (currentNode) {
      let data = currentNode.data;
      arrayForEach([MUSTACHE_EXPR, ERB_EXPR, TMPLIT_EXPR], (expr: RegExp) => {
        data = stringReplace(data, expr, ' ');
      });
      currentNode.data = data;
      currentNode = walker.nextNode() as CharacterData | null;
    }

    // NodeIterator does not descend into <template>.content per the DOM spec,
    // so we must explicitly recurse into each template's content fragment,
    // mirroring the approach used by _sanitizeShadowDOM.
    const templates = node.querySelectorAll?.('template') ?? [];
    arrayForEach(Array.from(templates), (tmpl: HTMLTemplateElement) => {
      if (_isDocumentFragment(tmpl.content)) {
        _scrubTemplateExpressions(tmpl.content as unknown as Element);
      }
    });
  };

  /**
   * _isClobbered
   *
   * @param element element to check for clobbering attacks
   * @return true if clobbered, false if safe
   */
  const _isClobbered = function (element: Element): boolean {
    // Realm-independent tag-name probe; `instanceof HTMLFormElement` is
    // false for forms from another realm (GHSA-hpcv-96wg-7vj8).
    const realTagName = getNodeName ? getNodeName(element) : null;
    if (typeof realTagName !== 'string') {
      return false;
    }

    if (transformCaseFunc(realTagName) !== 'form') {
      return false;
    }

    return (
      typeof element.nodeName !== 'string' ||
      typeof element.textContent !== 'string' ||
      typeof element.removeChild !== 'function' ||
      // Realm-safe NamedNodeMap detection: a clobbered .attributes diverges
      // from the cached prototype getter's read.
      element.attributes !== getAttributes(element) ||
      typeof element.removeAttribute !== 'function' ||
      typeof element.setAttribute !== 'function' ||
      typeof element.namespaceURI !== 'string' ||
      typeof element.insertBefore !== 'function' ||
      typeof element.hasChildNodes !== 'function' ||
      // NodeType clobbering probe. Cached Node.prototype.nodeType getter
      // returns the integer 1 for any Element regardless of realm; direct
      // read on a clobbered form (e.g. <input name="nodeType">) returns
      // the named child element. Cheap addition — nodeType is read from
      // an internal slot, no serialization cost — and removes a residual
      // clobbering surface used by several mXSS / PI / comment branches
      // in _sanitizeElements that compare currentNode.nodeType directly.
      element.nodeType !== getNodeType(element) ||
      // Form [LegacyOverrideBuiltIns]: a child named "childNodes" makes the
      // direct read diverge from the cached getter; typeof cannot see it.
      element.childNodes !== getChildNodes(element)
    );
  };

  /**
   * Checks whether the given value is a DocumentFragment from any realm.
   *
   * The realm-independent replacement reads `nodeType` through the cached
   * Node.prototype getter and compares to the DOCUMENT_FRAGMENT_NODE
   * constant (11). nodeType is a numeric value resolved from the node's
   * internal slot, identical across realms for the same kind of node.
   *
   * @param value object to check
   * @return true if value is a DocumentFragment-shaped node from any realm
   */
  const _isDocumentFragment = function (value: unknown): boolean {
    if (!getNodeType || typeof value !== 'object' || value === null) {
      return false;
    }

    try {
      return getNodeType(value as Node) === NODE_TYPE.documentFragment;
    } catch (_) {
      return false;
    }
  };

  /**
   * Checks whether the given object is a DOM node, including nodes that
   * originate from a different window/realm (e.g. an iframe's
   * contentDocument). The previous `value instanceof Node` check was
   * realm-bound: nodes from a different window failed it, causing
   * sanitize() to silently stringify them and reset IN_PLACE to false,
   * returning the original node unsanitized. See GHSA-4w3q-35jp-p934.
   *
   * Implementation: call the cached `nodeType` getter from Node.prototype
   * directly on the value. This bypasses any clobbered instance property
   * (e.g. a child element named "nodeType") and works across realms
   * because the WebIDL `nodeType` getter reads an internal slot that
   * every real Node has, regardless of which window minted it.
   *
   * @param value object to check whether it's a DOM node
   * @return true if value is a DOM node from any realm
   */
  const _isNode = function (value: unknown): value is Node {
    if (!getNodeType || typeof value !== 'object' || value === null) {
      return false;
    }

    try {
      return typeof getNodeType(value) === 'number';
    } catch (_) {
      return false;
    }
  };

  function _executeHooks<T extends HookFunction>(
    hooks: HookFunction[],
    currentNode: Parameters<T>[0],
    data: Parameters<T>[1]
  ): void {
    arrayForEach(hooks, (hook: T) => {
      hook.call(DOMPurify, currentNode, data, CONFIG);
    });
  }

  /**
   * Fork a hook-mutable allowlist off its shared binding the first time a
   * (possibly lazily-installed) uponSanitize* hook is about to see it, so the
   * hook cannot widen the per-instance default or the setConfig binding by
   * reference and leak past the call. Returns the set unchanged once it is
   * already call-local, so repeated calls across elements are idempotent.
   *
   * @param hookList the uponSanitize* hook array for this event
   * @param set the current ALLOWED_TAGS / ALLOWED_ATTR binding
   * @param defaultSet the per-instance DEFAULT_ALLOWED_* constant
   * @param setConfigSet the captured setConfig() binding, or null
   * @return a call-local clone if a hook is present and set is still shared,
   *   else set unchanged
   */
  const _forkSharedAllowlist = function <T extends Record<string, any>>(
    hookList: unknown[],
    set: T,
    defaultSet: T,
    setConfigSet: T | null
  ): T {
    if (hookList.length === 0) {
      return set;
    }

    return set === defaultSet || set === setConfigSet ? clone(set) : set;
  };

  /**
   * _sanitizeElements
   *
   * @protect nodeName
   * @protect textContent
   * @protect removeChild
   * @param currentNode to check for permission to exist
   * @return true if node was killed, false if left alive
   */
  // eslint-disable-next-line complexity
  const _sanitizeElements = function (currentNode: any, root: Node): boolean {
    let content = null;

    /* Execute a hook if present */
    _executeHooks(hooks.beforeSanitizeElements, currentNode, null);

    /* A hook may have detached the node - treat it as removed (see the
       detached-node comment after the uponSanitizeElement hook below). On
       the IN_PLACE path, neutralize the detached subtree first so a queued
       resource handler on it cannot fire in page scope after we return. */
    if (currentNode !== root && getParentNode(currentNode) === null) {
      if (IN_PLACE) {
        _neutralizeSubtree(currentNode);
      }

      return true;
    }

    /* Check if element is clobbered or can clobber */
    if (_isClobbered(currentNode)) {
      _forceRemove(currentNode);
      return true;
    }

    /* Now let's check the element's type and name */
    const tagName = transformCaseFunc(
      getNodeName ? getNodeName(currentNode) : currentNode.nodeName
    );

    /* Close the pre-walk clone-guard's timing gap: an uponSanitizeElement
       hook may have been installed after that guard sampled the hook arrays
       (e.g. lazily from beforeSanitizeElements), leaving ALLOWED_TAGS still
       aliasing a shared binding that a widening hook would mutate by
       reference. Fork it before exposing it to the hook. */
    ALLOWED_TAGS = _forkSharedAllowlist(
      hooks.uponSanitizeElement,
      ALLOWED_TAGS,
      DEFAULT_ALLOWED_TAGS,
      SET_CONFIG_ALLOWED_TAGS
    );

    /* Execute a hook if present */
    _executeHooks(hooks.uponSanitizeElement, currentNode, {
      tagName,
      allowedTags: ALLOWED_TAGS,
    });

    /* A hook may have detached the node from the tree (issue #469 pattern):
       treat it as removed and stop processing it. The walk root is exempt.
       Hook-detached nodes are not recorded in DOMPurify.removed. On the
       IN_PLACE path their subtree is neutralized inline here instead. */
    if (currentNode !== root && getParentNode(currentNode) === null) {
      if (IN_PLACE) {
        _neutralizeSubtree(currentNode);
      }

      return true;
    }

    /* Detect mXSS attempts abusing namespace confusion */
    if (
      SAFE_FOR_XML &&
      currentNode.hasChildNodes() &&
      !_isNode(currentNode.firstElementChild) &&
      regExpTest(/<[/\w!]/g, currentNode.innerHTML) &&
      regExpTest(/<[/\w!]/g, currentNode.textContent)
    ) {
      _forceRemove(currentNode);
      return true;
    }

    /* Remove rawtext/literal-text elements whose literal serialization
       re-opens markup on an HTML reparse - shapes (a) and (b) documented at
       LITERAL_TEXT_ELEMENTS. Both are invisible to rule 1 above (which
       self-disables once there is an element child, and whose second probe
       reads the innerHTML an XML/XHTML document serializes escaped), which
       is why both probes here read textContent instead. Previously only
       `style`-with-element-child was covered; every element in
       LITERAL_TEXT_ELEMENTS shares this literal serialization and is
       equally affected. */
    if (
      SAFE_FOR_XML &&
      currentNode.namespaceURI === HTML_NAMESPACE &&
      LITERAL_TEXT_ELEMENTS[tagName] &&
      (_isNode(currentNode.firstElementChild) ||
        (typeof currentNode.textContent === 'string' &&
          regExpTest(LITERAL_TEXT_CLOSE[tagName], currentNode.textContent)))
    ) {
      _forceRemove(currentNode);
      return true;
    }

    /* Remove any occurrence of processing instructions */
    if (currentNode.nodeType === NODE_TYPE.progressingInstruction) {
      _forceRemove(currentNode);
      return true;
    }

    /* Remove any kind of possibly harmful comments */
    if (
      SAFE_FOR_XML &&
      currentNode.nodeType === NODE_TYPE.comment &&
      regExpTest(/<[/\w]/g, currentNode.data)
    ) {
      _forceRemove(currentNode);
      return true;
    }

    /* Remove element if anything forbids its presence */
    if (
      FORBID_TAGS[tagName] ||
      (!(
        EXTRA_ELEMENT_HANDLING.tagCheck instanceof Function &&
        EXTRA_ELEMENT_HANDLING.tagCheck(tagName)
      ) &&
        !ALLOWED_TAGS[tagName])
    ) {
      /* Check if we have a custom element to handle */
      if (!FORBID_TAGS[tagName] && _isBasicCustomElement(tagName)) {
        if (
          CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof RegExp &&
          regExpTest(CUSTOM_ELEMENT_HANDLING.tagNameCheck, tagName)
        ) {
          /* A kept custom element still gets afterSanitizeElements, like any
             allowed element (GHSA-c2j3-45gr-mqc4). */
          _executeHooks(hooks.afterSanitizeElements, currentNode, null);
          return false;
        }

        if (
          CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof Function &&
          CUSTOM_ELEMENT_HANDLING.tagNameCheck(tagName)
        ) {
          _executeHooks(hooks.afterSanitizeElements, currentNode, null);
          return false;
        }
      }

      /* Keep content except for bad-listed elements.
         Use the cached prototype getters exclusively — the previous code
         had `|| currentNode.parentNode` / `|| currentNode.childNodes`
         fallbacks, but the cached getters always return the canonical
         value (or null for a real parent-less node), so the fallback
         path was dead in safe cases and a clobbering surface in unsafe
         ones. Falsy cached results stay falsy; the `if (childNodes &&
         parentNode)` check already gates correctly. */
      if (KEEP_CONTENT && !FORBID_CONTENTS[tagName]) {
        const parentNode = getParentNode(currentNode);
        const childNodes = getChildNodes(currentNode);

        if (childNodes && parentNode) {
          const childCount = childNodes.length;

          for (let i = childCount - 1; i >= 0; --i) {
            const childClone = cloneNode(childNodes[i], true);
            childClone.__removalCount = (currentNode.__removalCount || 0) + 1;
            parentNode.insertBefore(childClone, getNextSibling(currentNode));
          }
        }
      }

      _forceRemove(currentNode);
      return true;
    }

    /* Check whether element has a valid namespace.
       Realm-safe check (GHSA-hpcv-96wg-7vj8): nodeType, not instanceof. */
    const nt = getNodeType ? getNodeType(currentNode) : currentNode.nodeType;
    if (nt === NODE_TYPE.element && !_checkValidNamespace(currentNode)) {
      _forceRemove(currentNode);
      return true;
    }

    /* Make sure that older browsers don't get fallback-tag mXSS */
    if (
      (tagName === 'noscript' ||
        tagName === 'noembed' ||
        tagName === 'noframes') &&
      regExpTest(/<\/no(script|embed|frames)/i, currentNode.innerHTML)
    ) {
      _forceRemove(currentNode);
      return true;
    }

    /* Sanitize element content to be template-safe */
    if (SAFE_FOR_TEMPLATES && currentNode.nodeType === NODE_TYPE.text) {
      /* Get the element's text content */
      content = currentNode.textContent;

      arrayForEach([MUSTACHE_EXPR, ERB_EXPR, TMPLIT_EXPR], (expr: RegExp) => {
        content = stringReplace(content, expr, ' ');
      });

      if (currentNode.textContent !== content) {
        arrayPush(DOMPurify.removed, { element: currentNode.cloneNode() });
        currentNode.textContent = content;
      }
    }

    /* Execute a hook if present */
    _executeHooks(hooks.afterSanitizeElements, currentNode, null);

    return false;
  };

  /**
   * _isValidAttribute
   *
   * @param lcTag Lowercase tag name of containing element.
   * @param lcName Lowercase attribute name.
   * @param value Attribute value.
   * @return Returns true if `value` is valid, otherwise false.
   */
  // eslint-disable-next-line complexity
  const _isValidAttribute = function (
    lcTag: string,
    lcName: string,
    value: string
  ): boolean {
    /* FORBID_ATTR must always win, even if ADD_ATTR predicate would allow it */
    if (FORBID_ATTR[lcName]) {
      return false;
    }

    /* Make sure attribute cannot clobber */
    if (
      SANITIZE_DOM &&
      (lcName === 'id' || lcName === 'name') &&
      (value in document || value in formElement)
    ) {
      return false;
    }

    const nameIsPermitted =
      ALLOWED_ATTR[lcName] ||
      (EXTRA_ELEMENT_HANDLING.attributeCheck instanceof Function &&
        EXTRA_ELEMENT_HANDLING.attributeCheck(lcName, lcTag));

    /* Allow valid data-* attributes: At least one character after "-"
        (https://html.spec.whatwg.org/multipage/dom.html#embedding-custom-non-visible-data-with-the-data-*-attributes)
        XML-compatible (https://html.spec.whatwg.org/multipage/infrastructure.html#xml-compatible and http://www.w3.org/TR/xml/#d0e804)
        We don't need to check the value; it's always URI safe. */
    if (
      ALLOW_DATA_ATTR &&
      !FORBID_ATTR[lcName] &&
      regExpTest(DATA_ATTR, lcName)
    ) {
      // This attribute is safe
    } else if (ALLOW_ARIA_ATTR && regExpTest(ARIA_ATTR, lcName)) {
      // This attribute is safe
      /* Otherwise, check the name is permitted */
    } else if (!nameIsPermitted || FORBID_ATTR[lcName]) {
      if (
        // First condition does a very basic check if a) it's basically a valid custom element tagname AND
        // b) if the tagName passes whatever the user has configured for CUSTOM_ELEMENT_HANDLING.tagNameCheck
        // and c) if the attribute name passes whatever the user has configured for CUSTOM_ELEMENT_HANDLING.attributeNameCheck
        (_isBasicCustomElement(lcTag) &&
          ((CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof RegExp &&
            regExpTest(CUSTOM_ELEMENT_HANDLING.tagNameCheck, lcTag)) ||
            (CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof Function &&
              CUSTOM_ELEMENT_HANDLING.tagNameCheck(lcTag))) &&
          ((CUSTOM_ELEMENT_HANDLING.attributeNameCheck instanceof RegExp &&
            regExpTest(CUSTOM_ELEMENT_HANDLING.attributeNameCheck, lcName)) ||
            (CUSTOM_ELEMENT_HANDLING.attributeNameCheck instanceof Function &&
              CUSTOM_ELEMENT_HANDLING.attributeNameCheck(lcName, lcTag)))) ||
        // Alternative, second condition checks if it's an `is`-attribute, AND
        // the value passes whatever the user has configured for CUSTOM_ELEMENT_HANDLING.tagNameCheck
        (lcName === 'is' &&
          CUSTOM_ELEMENT_HANDLING.allowCustomizedBuiltInElements &&
          ((CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof RegExp &&
            regExpTest(CUSTOM_ELEMENT_HANDLING.tagNameCheck, value)) ||
            (CUSTOM_ELEMENT_HANDLING.tagNameCheck instanceof Function &&
              CUSTOM_ELEMENT_HANDLING.tagNameCheck(value))))
      ) {
        // If user has supplied a regexp or function in CUSTOM_ELEMENT_HANDLING.tagNameCheck, we need to also allow derived custom elements using the same tagName test.
        // Additionally, we need to allow attributes passing the CUSTOM_ELEMENT_HANDLING.attributeNameCheck user has configured, as custom elements can define these at their own discretion.
      } else {
        return false;
      }
      /* Check value is safe. First, is attr inert? If so, is safe */
    } else if (URI_SAFE_ATTRIBUTES[lcName]) {
      // This attribute is safe
      /* Check no script, data or unknown possibly unsafe URI
        unless we know URI values are safe for that attribute */
    } else if (
      regExpTest(IS_ALLOWED_URI, stringReplace(value, ATTR_WHITESPACE, ''))
    ) {
      // This attribute is safe
      /* Keep image data URIs alive if src/xlink:href is allowed */
      /* Further prevent gadget XSS for dynamically built script tags */
    } else if (
      (lcName === 'src' || lcName === 'xlink:href' || lcName === 'href') &&
      lcTag !== 'script' &&
      stringIndexOf(value, 'data:') === 0 &&
      DATA_URI_TAGS[lcTag]
    ) {
      // This attribute is safe
      /* Allow unknown protocols: This provides support for links that
        are handled by protocol handlers which may be unknown ahead of
        time, e.g. fb:, spotify: */
    } else if (
      ALLOW_UNKNOWN_PROTOCOLS &&
      !regExpTest(IS_SCRIPT_OR_DATA, stringReplace(value, ATTR_WHITESPACE, ''))
    ) {
      // This attribute is safe
      /* Check for binary attributes */
    } else if (value) {
      return false;
    } else {
      // Binary attributes are safe at this point
      /* Anything else, presume unsafe, do not add it back */
    }

    return true;
  };

  /**
   * _isBasicCustomElement
   * checks if at least one dash is included in tagName, and it's not the first char
   * for more sophisticated checking see https://github.com/sindresorhus/validate-element-name
   *
   * @param tagName name of the tag of the node to sanitize
   * @returns Returns true if the tag name meets the basic criteria for a custom element, otherwise false.
   */
  const _isBasicCustomElement = function (tagName: string): RegExpMatchArray {
    return tagName !== 'annotation-xml' && stringMatch(tagName, CUSTOM_ELEMENT);
  };

  /**
   * _sanitizeAttributes
   *
   * @protect attributes
   * @protect nodeName
   * @protect removeAttribute
   * @protect setAttribute
   *
   * @param currentNode to sanitize
   */
  const _sanitizeAttributes = function (currentNode: Element): void {
    /* Execute a hook if present */
    _executeHooks(hooks.beforeSanitizeAttributes, currentNode, null);

    const { attributes } = currentNode;

    /* Check if we have attributes; if not we might have a text node */
    if (!attributes || _isClobbered(currentNode)) {
      return;
    }

    /* Same lazy-install guard as uponSanitizeElement (see there): fork the
       attribute allowlist off its shared binding before a hook can see it. */
    ALLOWED_ATTR = _forkSharedAllowlist(
      hooks.uponSanitizeAttribute,
      ALLOWED_ATTR,
      DEFAULT_ALLOWED_ATTR,
      SET_CONFIG_ALLOWED_ATTR
    );

    const hookEvent = {
      attrName: '',
      attrValue: '',
      keepAttr: true,
      allowedAttributes: ALLOWED_ATTR,
      forceKeepAttr: undefined,
    };
    let l = attributes.length;

    /* Go backwards over all attributes; safely remove bad ones */
    while (l--) {
      const attr = attributes[l];
      const { name, namespaceURI, value: attrValue } = attr;
      const lcName = transformCaseFunc(name);

      const initValue = attrValue;
      let value = name === 'value' ? initValue : stringTrim(initValue);

      /* Execute a hook if present */
      hookEvent.attrName = lcName;
      hookEvent.attrValue = value;
      hookEvent.keepAttr = true;
      hookEvent.forceKeepAttr = undefined; // Allows developers to see this is a property they can set
      _executeHooks(hooks.uponSanitizeAttribute, currentNode, hookEvent);
      value = hookEvent.attrValue;

      /* Full DOM Clobbering protection via namespace isolation,
       * Prefix id and name attributes with `user-content-`
       */
      if (SANITIZE_NAMED_PROPS && (lcName === 'id' || lcName === 'name')) {
        // Remove the attribute with this value
        _removeAttribute(name, currentNode);

        // Prefix the value and later re-create the attribute with the sanitized value
        value = SANITIZE_NAMED_PROPS_PREFIX + value;
      }

      /* Work around a security issue with comments inside attributes */
      if (
        SAFE_FOR_XML &&
        regExpTest(
          /((--!?|])>)|<\/(style|script|title|xmp|textarea|noscript|iframe|noembed|noframes)/i,
          value
        )
      ) {
        _removeAttribute(name, currentNode);
        continue;
      }

      /* Make sure we cannot easily use animated hrefs, even if animations are
         allowed. Compared case-insensitively on purpose: in
         application/xhtml+xml mode lcName keeps its case, and the real SVG
         attribute is spelled attributeName, which 'attributename' would
         never match (GHSA-c6gr-qvv4-5v3f). In XHTML a lowercase
         `attributename` is not the SMIL attribute, so also stripping it
         there costs nothing. */
      if (
        stringToLowerCase(name) === 'attributename' &&
        stringMatch(value, 'href')
      ) {
        _removeAttribute(name, currentNode);
        continue;
      }

      /* Did the hooks approve of the attribute? */
      if (hookEvent.forceKeepAttr) {
        continue;
      }

      /* Did the hooks approve of the attribute? */
      if (!hookEvent.keepAttr) {
        _removeAttribute(name, currentNode);
        continue;
      }

      /* Work around a security issue in jQuery 3.0 */
      if (!ALLOW_SELF_CLOSE_IN_ATTR && regExpTest(/\/>/i, value)) {
        _removeAttribute(name, currentNode);
        continue;
      }

      /* Sanitize attribute content to be template-safe */
      if (SAFE_FOR_TEMPLATES) {
        arrayForEach([MUSTACHE_EXPR, ERB_EXPR, TMPLIT_EXPR], (expr: RegExp) => {
          value = stringReplace(value, expr, ' ');
        });
      }

      /* Is `value` valid for this attribute? */
      const lcTag = transformCaseFunc(
        getNodeName ? getNodeName(currentNode) : currentNode.nodeName
      );
      if (!_isValidAttribute(lcTag, lcName, value)) {
        _removeAttribute(name, currentNode);
        continue;
      }

      /* Handle attributes that require Trusted Types */
      if (
        trustedTypesPolicy &&
        typeof trustedTypes === 'object' &&
        typeof trustedTypes.getAttributeType === 'function'
      ) {
        if (namespaceURI) {
          /* Namespaces are not yet supported, see https://bugs.chromium.org/p/chromium/issues/detail?id=1305293 */
        } else {
          switch (trustedTypes.getAttributeType(lcTag, lcName)) {
            case 'TrustedHTML': {
              value = _createTrustedHTML(value);
              break;
            }

            case 'TrustedScriptURL': {
              value = _createTrustedScriptURL(value);
              break;
            }

            default: {
              break;
            }
          }
        }
      }

      /* Handle invalid data-* attribute set by try-catching it */
      if (value !== initValue) {
        try {
          if (namespaceURI) {
            currentNode.setAttributeNS(namespaceURI, name, value);
          } else {
            /* Fallback to setAttribute() for browser-unrecognized namespaces e.g. "x-schema". */
            currentNode.setAttribute(name, value);
          }

          if (_isClobbered(currentNode)) {
            _forceRemove(currentNode);
          } else {
            arrayPop(DOMPurify.removed);
          }
        } catch (_) {
          _removeAttribute(name, currentNode);
        }
      }
    }

    /* Execute a hook if present */
    _executeHooks(hooks.afterSanitizeAttributes, currentNode, null);
  };

  /**
   * _sanitizeShadowDOM
   *
   * @param fragment to iterate over recursively
   */
  const _sanitizeShadowDOM = function (fragment: DocumentFragment): void {
    let shadowNode = null;
    const shadowIterator = _createNodeIterator(fragment);

    /* Execute a hook if present */
    _executeHooks(hooks.beforeSanitizeShadowDOM, fragment, null);

    while ((shadowNode = shadowIterator.nextNode())) {
      /* Execute a hook if present */
      _executeHooks(hooks.uponSanitizeShadowNode, shadowNode, null);

      /* Sanitize tags and elements */
      _sanitizeElements(shadowNode, fragment);

      /* Check attributes next */
      _sanitizeAttributes(shadowNode);

      /* Deep shadow DOM detected.
         Realm-safe check (GHSA-hpcv-96wg-7vj8): nodeType, not instanceof. */
      if (_isDocumentFragment(shadowNode.content)) {
        _sanitizeShadowDOM(shadowNode.content);
      }

      /* NodeIterator does not enter shadow trees, so a shadow root hosted
         inside template.content is reached by no other walk; the nodeType
         guard skips text / comment / CDATA / PI nodes. */
      const shadowNodeType = getNodeType
        ? getNodeType(shadowNode)
        : (shadowNode as Node).nodeType;
      if (shadowNodeType === NODE_TYPE.element) {
        const innerSr = (shadowNode as Element).shadowRoot;
        if (_isDocumentFragment(innerSr)) {
          _sanitizeAttachedShadowRoots(innerSr);
          _sanitizeShadowDOM(innerSr);
        }
      }
    }

    /* Execute a hook if present */
    _executeHooks(hooks.afterSanitizeShadowDOM, fragment, null);
  };

  /**
   * _sanitizeAttachedShadowRoots
   *
   * Walks `root` and feeds every attached shadow root we encounter into
   * the existing _sanitizeShadowDOM pipeline. The default node iterator
   * does not descend into shadow trees, so nodes inside an attached
   * shadow root would otherwise be skipped entirely.
   *
   * Two real input paths put attached shadow roots in front of us:
   *   1. IN_PLACE on a DOM node that already has shadow roots attached.
   *   2. DOM-node input where importNode(dirty, true) deep-clones the
   *      shadow root because it was created with `clonable: true`.
   *
   * This pass runs once, up front, so the main iteration loop (and the
   * existing _sanitizeShadowDOM template-content recursion) stay
   * untouched — string-input paths are not affected.
   *
   * @param root the subtree root to walk for attached shadow roots
   */
  const _sanitizeAttachedShadowRoots = function (root: Node): void {
    const nodeType = getNodeType ? getNodeType(root) : (root as any).nodeType;

    if (
      nodeType === NODE_TYPE.element &&
      _isDocumentFragment((root as Element).shadowRoot)
    ) {
      const sr = (root as Element).shadowRoot as DocumentFragment;
      // Recurse first so that nested shadow roots are reached even if
      // _sanitizeShadowDOM removes hosts at this level.
      _sanitizeAttachedShadowRoots(sr);
      _sanitizeShadowDOM(sr);
    }

    // Snapshot children before recursing. Sanitization of one subtree
    // (e.g. via an uponSanitizeShadowNode hook) may detach siblings,
    // and naive nextSibling traversal would silently skip the rest of
    // the list once a node is detached.
    const childNodes = root.childNodes;
    if (!childNodes) {
      return;
    }

    const snapshot: Node[] = [];
    arrayForEach(childNodes, (child) => {
      arrayPush(snapshot, child);
    });

    for (const child of snapshot) {
      _sanitizeAttachedShadowRoots(child);
    }

    /* When the root is a <template>, also descend into root.content */
    if (nodeType === NODE_TYPE.element) {
      const rootName = getNodeName ? getNodeName(root) : null;
      if (
        typeof rootName === 'string' &&
        transformCaseFunc(rootName) === 'template'
      ) {
        const content = (root as HTMLTemplateElement).content;
        if (_isDocumentFragment(content)) {
          _sanitizeAttachedShadowRoots(content);
        }
      }
    }
  };

  // eslint-disable-next-line complexity
  DOMPurify.sanitize = function (dirty, cfg = {}) {
    let body = null;
    let importedNode = null;
    let currentNode = null;
    let returnNode = null;
    /* Make sure we have a string to sanitize.
      DO NOT return early, as this will return the wrong type if
      the user has requested a DOM object rather than a string */
    IS_EMPTY_INPUT = !dirty;
    if (IS_EMPTY_INPUT) {
      dirty = '<!-->';
    }

    /* Stringify, in case dirty is an object */
    if (typeof dirty !== 'string' && !_isNode(dirty)) {
      if (typeof dirty.toString === 'function') {
        dirty = dirty.toString();
        if (typeof dirty !== 'string') {
          throw typeErrorCreate('dirty is not a string, aborting');
        }
      } else {
        throw typeErrorCreate('toString is not a function');
      }
    }

    /* Return dirty HTML if DOMPurify cannot run */
    if (!DOMPurify.isSupported) {
      return dirty;
    }

    /* Assign config vars */
    if (SET_CONFIG) {
      /* Persistent setConfig() path: _parseConfig is skipped, so the sets are
       * not re-derived per call. Restore them from the pristine bindings
       * captured at setConfig() time so a previous call's hook clone (mutated
       * below) does not carry over. */
      ALLOWED_TAGS = SET_CONFIG_ALLOWED_TAGS;
      ALLOWED_ATTR = SET_CONFIG_ALLOWED_ATTR;
    } else {
      _parseConfig(cfg);
    }

    /* Clone the hook-mutable allowlists before the walk whenever an
     * uponSanitize* hook is registered. The hook event exposes ALLOWED_TAGS
     * and ALLOWED_ATTR by reference (as allowedTags / allowedAttributes), so
     * a hook that widens them would otherwise mutate the shared set
     * permanently: across later calls and across every element. Cloning per
     * walk keeps documented in-call widening working while scoping it to the
     * call. A single guard for both config paths - the per-call path rebinds
     * the sets in _parseConfig each call, the persistent path restores them
     * from the captured bindings just above - so the two cannot diverge. */
    if (
      hooks.uponSanitizeElement.length > 0 ||
      hooks.uponSanitizeAttribute.length > 0
    ) {
      ALLOWED_TAGS = clone(ALLOWED_TAGS);
    }

    if (hooks.uponSanitizeAttribute.length > 0) {
      ALLOWED_ATTR = clone(ALLOWED_ATTR);
    }

    /* Clean up removed elements */
    DOMPurify.removed = [];

    /* Resolved per call: writing IN_PLACE here would leak under setConfig(),
       and one string call would leave later in-place nodes unsanitized. */
    const inPlace = IN_PLACE && typeof dirty !== 'string' && _isNode(dirty);

    if (inPlace) {
      /* Do some early pre-sanitization to avoid unsafe root nodes.
         Read nodeName via the cached prototype getter: an own or clobbered
         nodeName on the root must not skip the root-allowlist check. */
      const nn = getNodeName
        ? getNodeName(dirty as Node)
        : (dirty as Node).nodeName;
      if (nn) {
        const tagName = transformCaseFunc(nn);
        if (!ALLOWED_TAGS[tagName] || FORBID_TAGS[tagName]) {
          throw typeErrorCreate(
            'root node is forbidden and cannot be sanitized in-place'
          );
        }
      }

      /* A parent-less root cannot be removed by _forceRemove, and
         _sanitizeAttributes skips clobbered nodes, so refuse it here. */
      if (_isClobbered(dirty as Element)) {
        throw typeErrorCreate(
          'root node is clobbered and cannot be sanitized in-place'
        );
      }

      /* Sanitize attached shadow roots before the main iterator runs.
         The iterator does not descend into shadow trees. */
      _sanitizeAttachedShadowRoots(dirty as Node);
    } else if (_isNode(dirty)) {
      /* If dirty is a DOM element, append to an empty document to avoid
         elements being stripped by the parser */
      body = _initDocument('<!---->');
      importedNode = body.ownerDocument.importNode(dirty, true);
      if (
        importedNode.nodeType === NODE_TYPE.element &&
        importedNode.nodeName === 'BODY'
      ) {
        /* Node is already a body, use as is */
        body = importedNode;
      } else if (importedNode.nodeName === 'HTML') {
        body = importedNode;
      } else {
        // eslint-disable-next-line unicorn/prefer-dom-node-append
        body.appendChild(importedNode);
      }

      /* Clonable shadow roots are deep-cloned by importNode(); sanitize
         them before the main iterator runs, since the iterator does not
         descend into shadow trees. */
      _sanitizeAttachedShadowRoots(importedNode);
    } else {
      /* Exit directly if we have nothing to do */
      if (
        !RETURN_DOM &&
        !SAFE_FOR_TEMPLATES &&
        !WHOLE_DOCUMENT &&
        // eslint-disable-next-line unicorn/prefer-includes
        dirty.indexOf('<') === -1
      ) {
        return trustedTypesPolicy && RETURN_TRUSTED_TYPE
          ? _createTrustedHTML(dirty)
          : dirty;
      }

      /* Initialize the document to work on */
      body = _initDocument(dirty);

      /* Check we have a DOM node from the data */
      if (!body) {
        return RETURN_DOM ? null : RETURN_TRUSTED_TYPE ? emptyHTML : '';
      }
    }

    /* Remove first element node (ours) if FORCE_BODY is set */
    if (body && FORCE_BODY) {
      _forceRemove(body.firstChild);
    }

    /* Get node iterator */
    const walkRoot: Node = inPlace ? (dirty as Node) : body;
    const nodeIterator = _createNodeIterator(walkRoot);

    /* Now start iterating over the created document */
    while ((currentNode = nodeIterator.nextNode())) {
      /* Sanitize tags and elements */
      _sanitizeElements(currentNode, walkRoot);

      /* Check attributes next */
      _sanitizeAttributes(currentNode);

      /* Shadow DOM detected, sanitize it.
         Realm-safe check (GHSA-hpcv-96wg-7vj8): nodeType, not instanceof. */
      if (_isDocumentFragment(currentNode.content)) {
        _sanitizeShadowDOM(currentNode.content);
      }
    }

    /* If we sanitized `dirty` in-place, return it. */
    if (inPlace) {
      /* A force-removed root (mXSS canary, clobbered, ...) is detached and may
         still carry a literal `</tag>` payload; there is no safe node to hand
         back, so fail closed instead of returning it. */
      let rootWasRemoved = false;
      arrayForEach(DOMPurify.removed, (entry) => {
        if (entry.element && entry.element === dirty) {
          rootWasRemoved = true;
        }
      });

      if (rootWasRemoved) {
        throw typeErrorCreate(
          'a node selected for removal could not be safely returned; ' +
            'refusing to sanitize in place'
        );
      }

      if (SAFE_FOR_TEMPLATES) {
        _scrubTemplateExpressions(dirty as Element);
      }

      return dirty;
    }

    /* Return sanitized string or DOM */
    if (RETURN_DOM) {
      if (SAFE_FOR_TEMPLATES) {
        _scrubTemplateExpressions(body);
      }

      if (RETURN_DOM_FRAGMENT) {
        returnNode = createDocumentFragment.call(body.ownerDocument);

        while (body.firstChild) {
          // eslint-disable-next-line unicorn/prefer-dom-node-append
          returnNode.appendChild(body.firstChild);
        }
      } else {
        returnNode = body;
      }

      if (ALLOWED_ATTR.shadowroot || ALLOWED_ATTR.shadowrootmode) {
        /*
          AdoptNode() is not used because internal state is not reset
          (e.g. the past names map of a HTMLFormElement), this is safe
          in theory but we would rather not risk another attack vector.
          The state that is cloned by importNode() is explicitly defined
          by the specs.
        */
        returnNode = importNode.call(originalDocument, returnNode, true);
      }

      return returnNode;
    }

    let serializedHTML = WHOLE_DOCUMENT ? body.outerHTML : body.innerHTML;

    /* Serialize doctype if allowed */
    if (
      WHOLE_DOCUMENT &&
      ALLOWED_TAGS['!doctype'] &&
      body.ownerDocument &&
      body.ownerDocument.doctype &&
      body.ownerDocument.doctype.name &&
      regExpTest(EXPRESSIONS.DOCTYPE_NAME, body.ownerDocument.doctype.name)
    ) {
      serializedHTML =
        '<!DOCTYPE ' + body.ownerDocument.doctype.name + '>\n' + serializedHTML;
    }

    /* Sanitize final string template-safe */
    if (SAFE_FOR_TEMPLATES) {
      arrayForEach([MUSTACHE_EXPR, ERB_EXPR, TMPLIT_EXPR], (expr: RegExp) => {
        serializedHTML = stringReplace(serializedHTML, expr, ' ');
      });
    }

    return trustedTypesPolicy && RETURN_TRUSTED_TYPE
      ? _createTrustedHTML(serializedHTML)
      : serializedHTML;
  };

  DOMPurify.setConfig = function (cfg = {}) {
    _parseConfig(cfg);
    SET_CONFIG = true;
    SET_CONFIG_ALLOWED_TAGS = ALLOWED_TAGS;
    SET_CONFIG_ALLOWED_ATTR = ALLOWED_ATTR;
  };

  DOMPurify.clearConfig = function () {
    CONFIG = null;
    SET_CONFIG = false;
    SET_CONFIG_ALLOWED_TAGS = null;
    SET_CONFIG_ALLOWED_ATTR = null;

    // Drop a caller policy so it cannot sign later RETURN_TRUSTED_TYPE output;
    // the cached internal one is restored. See GHSA-vxr8-fq34-vvx9.
    trustedTypesPolicy = defaultTrustedTypesPolicy;
    emptyHTML = '';
  };

  DOMPurify.isValidAttribute = function (tag, attr, value) {
    /* Initialize shared config vars if necessary. */
    if (!CONFIG) {
      _parseConfig({});
    }

    const lcTag = transformCaseFunc(tag);
    const lcName = transformCaseFunc(attr);
    return _isValidAttribute(lcTag, lcName, value);
  };

  DOMPurify.addHook = function (
    entryPoint: keyof HooksMap,
    hookFunction: HookFunction
  ) {
    if (typeof hookFunction !== 'function') {
      return;
    }

    /* Reject unknown entry points. Without this, a non-hook key (e.g.
     * '__proto__') indexes off the prototype chain rather than a real
     * hook array, and arrayPush then writes to Object.prototype. Guard
     * with an own-property check against the known hook names. */
    if (!objectHasOwnProperty(hooks, entryPoint)) {
      return;
    }

    arrayPush(hooks[entryPoint], hookFunction);
  };

  DOMPurify.removeHook = function (
    entryPoint: keyof HooksMap,
    hookFunction: HookFunction
  ) {
    if (!objectHasOwnProperty(hooks, entryPoint)) {
      return undefined;
    }

    if (hookFunction !== undefined) {
      const index = arrayLastIndexOf(hooks[entryPoint], hookFunction);

      return index === -1
        ? undefined
        : arraySplice(hooks[entryPoint], index, 1)[0];
    }

    return arrayPop(hooks[entryPoint]);
  };

  DOMPurify.removeHooks = function (entryPoint: keyof HooksMap) {
    if (!objectHasOwnProperty(hooks, entryPoint)) {
      return;
    }

    hooks[entryPoint] = [];
  };

  DOMPurify.removeAllHooks = function () {
    hooks = _createHooksMap();
  };

  return DOMPurify;
}

export default createDOMPurify();

export interface DOMPurify {
  /**
   * Creates a DOMPurify instance using the given window-like object. Defaults to `window`.
   */
  (root?: WindowLike): DOMPurify;

  /**
   * Version label, exposed for easier checks
   * if DOMPurify is up to date or not
   */
  version: string;

  /**
   * Array of elements that DOMPurify removed during sanitation.
   * Empty if nothing was removed.
   */
  removed: Array<RemovedElement | RemovedAttribute>;

  /**
   * Expose whether this browser supports running the full DOMPurify.
   */
  isSupported: boolean;

  /**
   * Set the configuration once.
   *
   * @param cfg configuration object
   */
  setConfig(cfg?: Config): void;

  /**
   * Removes the configuration.
   */
  clearConfig(): void;

  /**
   * Provides core sanitation functionality.
   *
   * @param dirty string or DOM node
   * @param cfg object
   * @returns Sanitized TrustedHTML.
   */
  sanitize(
    dirty: string | Node,
    cfg: Config & { RETURN_TRUSTED_TYPE: true }
  ): TrustedHTML;

  /**
   * Provides core sanitation functionality.
   *
   * @param dirty DOM node
   * @param cfg object
   * @returns Sanitized DOM node.
   */
  sanitize(dirty: Node, cfg: Config & { IN_PLACE: true }): Node;

  /**
   * Provides core sanitation functionality.
   *
   * @param dirty string or DOM node
   * @param cfg object
   * @returns Sanitized DOM node.
   */
  sanitize(dirty: string | Node, cfg: Config & { RETURN_DOM: true }): Node;

  /**
   * Provides core sanitation functionality.
   *
   * @param dirty string or DOM node
   * @param cfg object
   * @returns Sanitized document fragment.
   */
  sanitize(
    dirty: string | Node,
    cfg: Config & { RETURN_DOM_FRAGMENT: true }
  ): DocumentFragment;

  /**
   * Provides core sanitation functionality.
   *
   * @param dirty string or DOM node
   * @param cfg object
   * @returns Sanitized string.
   */
  sanitize(dirty: string | Node, cfg?: Config): string;

  /**
   * Checks if an attribute value is valid.
   * Uses last set config, if any. Otherwise, uses config defaults.
   *
   * @param tag Tag name of containing element.
   * @param attr Attribute name.
   * @param value Attribute value.
   * @returns Returns true if `value` is valid. Otherwise, returns false.
   */
  isValidAttribute(tag: string, attr: string, value: string): boolean;

  /**
   * Adds a DOMPurify hook.
   *
   * @param entryPoint entry point for the hook to add
   * @param hookFunction function to execute
   */
  addHook(entryPoint: BasicHookName, hookFunction: NodeHook): void;

  /**
   * Adds a DOMPurify hook.
   *
   * @param entryPoint entry point for the hook to add
   * @param hookFunction function to execute
   */
  addHook(entryPoint: ElementHookName, hookFunction: ElementHook): void;

  /**
   * Adds a DOMPurify hook.
   *
   * @param entryPoint entry point for the hook to add
   * @param hookFunction function to execute
   */
  addHook(
    entryPoint: DocumentFragmentHookName,
    hookFunction: DocumentFragmentHook
  ): void;

  /**
   * Adds a DOMPurify hook.
   *
   * @param entryPoint entry point for the hook to add
   * @param hookFunction function to execute
   */
  addHook(
    entryPoint: 'uponSanitizeElement',
    hookFunction: UponSanitizeElementHook
  ): void;

  /**
   * Adds a DOMPurify hook.
   *
   * @param entryPoint entry point for the hook to add
   * @param hookFunction function to execute
   */
  addHook(
    entryPoint: 'uponSanitizeAttribute',
    hookFunction: UponSanitizeAttributeHook
  ): void;

  /**
   * Remove a DOMPurify hook at a given entryPoint
   * (pops it from the stack of hooks if hook not specified)
   *
   * @param entryPoint entry point for the hook to remove
   * @param hookFunction optional specific hook to remove
   * @returns removed hook
   */
  removeHook(
    entryPoint: BasicHookName,
    hookFunction?: NodeHook
  ): NodeHook | undefined;

  /**
   * Remove a DOMPurify hook at a given entryPoint
   * (pops it from the stack of hooks if hook not specified)
   *
   * @param entryPoint entry point for the hook to remove
   * @param hookFunction optional specific hook to remove
   * @returns removed hook
   */
  removeHook(
    entryPoint: ElementHookName,
    hookFunction?: ElementHook
  ): ElementHook | undefined;

  /**
   * Remove a DOMPurify hook at a given entryPoint
   * (pops it from the stack of hooks if hook not specified)
   *
   * @param entryPoint entry point for the hook to remove
   * @param hookFunction optional specific hook to remove
   * @returns removed hook
   */
  removeHook(
    entryPoint: DocumentFragmentHookName,
    hookFunction?: DocumentFragmentHook
  ): DocumentFragmentHook | undefined;

  /**
   * Remove a DOMPurify hook at a given entryPoint
   * (pops it from the stack of hooks if hook not specified)
   *
   * @param entryPoint entry point for the hook to remove
   * @param hookFunction optional specific hook to remove
   * @returns removed hook
   */
  removeHook(
    entryPoint: 'uponSanitizeElement',
    hookFunction?: UponSanitizeElementHook
  ): UponSanitizeElementHook | undefined;

  /**
   * Remove a DOMPurify hook at a given entryPoint
   * (pops it from the stack of hooks if hook not specified)
   *
   * @param entryPoint entry point for the hook to remove
   * @param hookFunction optional specific hook to remove
   * @returns removed hook
   */
  removeHook(
    entryPoint: 'uponSanitizeAttribute',
    hookFunction?: UponSanitizeAttributeHook
  ): UponSanitizeAttributeHook | undefined;

  /**
   * Removes all DOMPurify hooks at a given entryPoint
   *
   * @param entryPoint entry point for the hooks to remove
   */
  removeHooks(entryPoint: HookName): void;

  /**
   * Removes all DOMPurify hooks.
   */
  removeAllHooks(): void;
}

/**
 * An element removed by DOMPurify.
 */
export interface RemovedElement {
  /**
   * The element that was removed.
   */
  element: Node;
}

/**
 * An element removed by DOMPurify.
 */
export interface RemovedAttribute {
  /**
   * The attribute that was removed.
   */
  attribute: Attr | null;

  /**
   * The element that the attribute was removed.
   */
  from: Node;
}

type BasicHookName =
  | 'beforeSanitizeElements'
  | 'afterSanitizeElements'
  | 'uponSanitizeShadowNode';
type ElementHookName = 'beforeSanitizeAttributes' | 'afterSanitizeAttributes';
type DocumentFragmentHookName =
  | 'beforeSanitizeShadowDOM'
  | 'afterSanitizeShadowDOM';
type UponSanitizeElementHookName = 'uponSanitizeElement';
type UponSanitizeAttributeHookName = 'uponSanitizeAttribute';

interface HooksMap {
  beforeSanitizeElements: NodeHook[];
  afterSanitizeElements: NodeHook[];
  beforeSanitizeShadowDOM: DocumentFragmentHook[];
  uponSanitizeShadowNode: NodeHook[];
  afterSanitizeShadowDOM: DocumentFragmentHook[];
  beforeSanitizeAttributes: ElementHook[];
  afterSanitizeAttributes: ElementHook[];
  uponSanitizeElement: UponSanitizeElementHook[];
  uponSanitizeAttribute: UponSanitizeAttributeHook[];
}

type ArrayElement<T> = T extends Array<infer U> ? U : never;

type HookFunction = ArrayElement<HooksMap[keyof HooksMap]>;

export type HookName =
  | BasicHookName
  | ElementHookName
  | DocumentFragmentHookName
  | UponSanitizeElementHookName
  | UponSanitizeAttributeHookName;

export type NodeHook = (
  this: DOMPurify,
  currentNode: Node,
  hookEvent: null,
  config: Config
) => void;

export type ElementHook = (
  this: DOMPurify,
  currentNode: Element,
  hookEvent: null,
  config: Config
) => void;

export type DocumentFragmentHook = (
  this: DOMPurify,
  currentNode: DocumentFragment,
  hookEvent: null,
  config: Config
) => void;

export type UponSanitizeElementHook = (
  this: DOMPurify,
  currentNode: Node,
  hookEvent: UponSanitizeElementHookEvent,
  config: Config
) => void;

export type UponSanitizeAttributeHook = (
  this: DOMPurify,
  currentNode: Element,
  hookEvent: UponSanitizeAttributeHookEvent,
  config: Config
) => void;

export interface UponSanitizeElementHookEvent {
  tagName: string;
  allowedTags: Record<string, boolean>;
}

export interface UponSanitizeAttributeHookEvent {
  attrName: string;
  attrValue: string;
  keepAttr: boolean;
  allowedAttributes: Record<string, boolean>;
  forceKeepAttr: boolean | undefined;
}

/**
 * A `Window`-like object containing the properties and types that DOMPurify requires.
 */
export type WindowLike = Pick<
  typeof globalThis,
  | 'DocumentFragment'
  | 'HTMLTemplateElement'
  | 'Node'
  | 'Element'
  | 'NodeFilter'
  | 'NamedNodeMap'
  | 'HTMLFormElement'
  | 'DOMParser'
> & {
  document?: Document;
  MozNamedAttrMap?: typeof window.NamedNodeMap;
} & Pick<TrustedTypesWindow, 'trustedTypes'>;
