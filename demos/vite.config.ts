import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// GH Pages serves from /sal/demos/: base path set accordingly for prod build.
export default defineConfig(({ command }) => ({
  plugins: [react()],
  base: command === "build" ? "/sal/" : "/",
  test: {
    globals: true,
    environment: "node",
  },
}));
