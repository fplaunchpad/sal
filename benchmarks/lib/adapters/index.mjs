// Adapter registry: dynamic import so a worker only loads the system it
// benchmarks (keeps heap/wasm isolation per child process).

export const SYSTEMS = ['rga', 'embed-rga', 'sided-embed-rga', 'sal', 'sal-shared', 'sal-sided', 'sal-sided-shared', 'sal-sided-unified', 'yjs', 'automerge', 'loro', 'listpositions'];

export async function getAdapter(name) {
  switch (name) {
    case 'rga': return (await import('./sal.mjs')).mkAdapter({ plainRGA: true });
    case 'embed-rga': return (await import('./sal.mjs')).mkAdapter({ shared: true });
    case 'sided-embed-rga': return (await import('./sal.mjs')).mkAdapter({ sided: true, shared: true, unified: true });
    case 'sal': return (await import('./sal.mjs')).mkAdapter();
    case 'sal-shared': return (await import('./sal.mjs')).mkAdapter({ shared: true });
    case 'sal-sided': return (await import('./sal.mjs')).mkAdapter({ sided: true });
    case 'sal-sided-shared': return (await import('./sal.mjs')).mkAdapter({ sided: true, shared: true });
    case 'sal-sided-unified': return (await import('./sal.mjs')).mkAdapter({ sided: true, shared: true, unified: true });
    case 'yjs': return (await import('./yjs.mjs')).mkAdapter();
    case 'automerge': return (await import('./automerge.mjs')).mkAdapter();
    case 'loro': return (await import('./loro.mjs')).mkAdapter();
    case 'listpositions': return (await import('./listpositions.mjs')).mkAdapter();
    default: throw new Error(`unknown system: ${name}`);
  }
}

export const byteLength = (data) =>
  typeof data === 'string' ? Buffer.byteLength(data, 'utf8') : data.length;
