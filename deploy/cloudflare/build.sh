#!/bin/sh -e
# Stage the browser-served tree into public/ preserving the exact URL paths
# the editor uses (/p2p-demo/..., /runtime/...): the app sources, the runtime
# ESM, and the prosemirror ESM the import map points into node_modules.
cd "$(dirname "$0")"
ROOT=../..

rm -rf public
mkdir -p public/p2p-demo public/runtime

cp -R "$ROOT/p2p-demo/web" public/p2p-demo/web
cp -R "$ROOT/p2p-demo/src" public/p2p-demo/src
cp -R "$ROOT/runtime/src" public/runtime/src

for p in prosemirror-model prosemirror-state prosemirror-transform \
         prosemirror-view prosemirror-keymap prosemirror-commands orderedmap; do
  mkdir -p "public/p2p-demo/node_modules/$p/dist"
  cp "$ROOT/p2p-demo/node_modules/$p/dist/index.js" "public/p2p-demo/node_modules/$p/dist/"
done
mkdir -p public/p2p-demo/node_modules/w3c-keyname
cp "$ROOT/p2p-demo/node_modules/w3c-keyname/index.js" public/p2p-demo/node_modules/w3c-keyname/
mkdir -p public/p2p-demo/node_modules/prosemirror-view/style
cp "$ROOT/p2p-demo/node_modules/prosemirror-view/style/prosemirror.css" \
   public/p2p-demo/node_modules/prosemirror-view/style/

echo "staged $(find public -type f | wc -l | tr -d ' ') files into public/"
