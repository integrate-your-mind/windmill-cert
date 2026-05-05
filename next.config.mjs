import path from "node:path";
import { fileURLToPath } from "node:url";

const configRoot = path.dirname(fileURLToPath(import.meta.url));

/** @type {import('next').NextConfig} */
const nextConfig = {
  output: "export",
  trailingSlash: true,
  assetPrefix: process.env.NODE_ENV === "production" ? "./" : undefined,
  turbopack: {
    root: configRoot,
  },
};

export default nextConfig;
