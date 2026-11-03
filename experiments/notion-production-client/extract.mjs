import { parse } from 'acorn';
import { createHash } from 'node:crypto';
import { readFileSync, mkdirSync, writeFileSync, copyFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export function extract(cache) {
  const manifest = JSON.parse(readFileSync(new URL('./sources.json', import.meta.url)));
  const modules = {};
  for (const asset of manifest.assets) {
    const bytes = readFileSync(resolve(cache, asset.file));
    if (bytes.length !== asset.bytes || createHash('sha256').update(bytes).digest('hex') !== asset.sha256)
      throw new Error(`Source mismatch: ${asset.file}`);
    const source = bytes.toString('utf8');
    const ast = parse(source, { ecmaVersion: 'latest', sourceType: 'script' });
    function registry(object) {
      if (object?.type !== 'ObjectExpression') return;
      if (!object.properties.length || !object.properties.every(p =>
        p.type === 'Property' && p.key.type === 'Literal' && Number.isInteger(p.key.value) &&
        p.value.type === 'FunctionExpression')) return;
      for (const property of object.properties) {
        const id = String(property.key.value);
        const text = source.slice(property.start, property.end);
        if (modules[id] && modules[id].source !== text)
          throw new Error(`Conflicting module ${id}: ${modules[id].file}:${modules[id].start} versus ${asset.file}:${property.start}`);
        modules[id] = { source: text, file: asset.file, start: property.start, end: property.end };
      }
    }
    function visit(node) {
      if (!node || typeof node !== 'object') return;
      if (node.type === 'CallExpression' && node.callee.type === 'MemberExpression' &&
          node.callee.property.name === 'push' && node.arguments[0]?.type === 'ArrayExpression')
        registry(node.arguments[0].elements[1]);
      if (node.type === 'VariableDeclarator') registry(node.init);
      for (const value of Object.values(node)) {
        if (Array.isArray(value)) value.forEach(visit);
        else if (value && typeof value === 'object') visit(value);
      }
    }
    visit(ast);
  }
  for (const id of Object.values(manifest.roots))
    if (!modules[id]) throw new Error(`Missing root module ${id}`);
  return { roots: manifest.roots, modules };
}

export function exportLibrary(cache, destination) {
  const result = extract(cache);
  // Refuse an existing directory, so exporting cannot overwrite a prior run.
  mkdirSync(destination);
  writeFileSync(resolve(destination, 'modules.json'), JSON.stringify(result));
  for (const file of ['runtime.mjs', 'client.mjs', 'requests.mjs', 'index.mjs', 'sources.json'])
    copyFileSync(new URL(file, import.meta.url), resolve(destination, file));
  return result;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const [cache, destination] = process.argv.slice(2);
  if (!cache || !destination) throw new Error('Usage: node extract.mjs CACHE OUTPUT_DIRECTORY');
  const result = exportLibrary(cache, destination);
  console.log(`Exported ${Object.keys(result.modules).length} original module bodies to ${destination}`);
}
