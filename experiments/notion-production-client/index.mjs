import { readFileSync } from 'node:fs';
import { ProductionClient } from './client.mjs';
export { RequestBuilder } from './requests.mjs';

const extracted = JSON.parse(readFileSync(new URL('./modules.json', import.meta.url)));
export const provenance = JSON.parse(readFileSync(new URL('./sources.json', import.meta.url)));
export function createClient(session, snapshot) {
  return new ProductionClient(extracted, session, snapshot);
}
