import vm from 'node:vm';

// Bundler glue only. Editing functions are compiled from exact source slices.
// Missing imports fail; no editing dependency has a fallback implementation.
export function createRuntime(extracted) {
  const timer = (callback, delay, ...args) => {
    const handle = setTimeout(callback, delay, ...args);
    handle.unref();
    return handle;
  };
  const context = vm.createContext({ URL, URLSearchParams, TextEncoder, TextDecoder, DOMException, performance,
    atob, btoa, structuredClone, setTimeout: timer, clearTimeout, crypto: globalThis.crypto },
    { codeGeneration: { strings: false, wasm: false } });
  const loaded = new Map();
  const loading = [];
  function require(id) {
    id = String(id);
    if (loaded.has(id)) return loaded.get(id).exports;
    const original = extracted.modules[id];
    if (!original) throw new Error(`Missing production module ${id}; required by ${loading.join(' -> ')}`);
    const module = { exports: {} };
    loaded.set(id, module);
    loading.push(id);
    try {
      const factory = new vm.Script(`({${original.source}})[${id}]`, {
        filename: `${original.file}:module-${id}`,
      }).runInContext(context, { timeout: 3000 });
      factory.call(module.exports, module, module.exports, require);
      return module.exports;
    } catch (error) {
      loaded.delete(id);
      throw error;
    } finally { loading.pop(); }
  }
  require.d = (exports, definitions = {}, values = {}) => {
    for (const [key, getter] of Object.entries(definitions))
      if (!Object.hasOwn(exports, key)) Object.defineProperty(exports, key, { enumerable: true, get: getter });
    for (const [key, value] of Object.entries(values))
      if (!Object.hasOwn(exports, key)) Object.defineProperty(exports, key, { enumerable: true, value });
  };
  require.r = exports => {
    Object.defineProperty(exports, '__esModule', { value: true });
    Object.defineProperty(exports, Symbol.toStringTag, { value: 'Module' });
  };
  require.o = (object, key) => Object.hasOwn(object, key);
  require.n = module => { const getter = module?.__esModule ? () => module.default : () => module; require.d(getter, { a: getter }); return getter; };
  require.g = vm.runInContext('globalThis', context);
  // Observe request construction at its transaction-output boundary. The
  // factory and its editing helpers remain verbatim; the caller supplies a
  // named dependency seam rather than silently falling back for imports.
  function instantiate(id, imports = {}) {
    id = String(id);
    const original = extracted.modules[id];
    if (!original) throw new Error(`Missing production module ${id}`);
    const dependency = Object.assign(key => Object.hasOwn(imports, String(key)) ?
      imports[String(key)] : require(key), require);
    const module = { exports: {} };
    const factory = new vm.Script(`({${original.source}})[${id}]`, {
      filename: `${original.file}:module-${id}:observed`,
    }).runInContext(context, { timeout: 3000 });
    factory.call(module.exports, module, module.exports, dependency);
    return module.exports;
  }
  return { require, loaded, context, instantiate };
}
