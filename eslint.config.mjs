import { defineConfig, globalIgnores } from "eslint/config";
import nextVitals from "eslint-config-next/core-web-vitals";

export default defineConfig([
  ...nextVitals,
  globalIgnores([
    ".next/**",
    ".lake/**",
    "out/**",
    "build/**",
    "artifacts/**",
    "next-env.d.ts",
  ]),
]);
