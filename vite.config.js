import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// Standard Vite + React config. No special build options are required:
// the app is a single default-export component with no CSS-file imports,
// no env vars, and no extra dependencies beyond react/react-dom.
export default defineConfig({
  plugins: [react()],
});
