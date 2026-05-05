import { cp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";

const root = process.cwd();
const outDir = path.join(root, "out");
const exportDir = path.join(root, "artifacts", "next-demo");
const certificatePath = path.join(root, "artifacts", "sample_certificate.json");
const gifPath = path.join(root, "artifacts", "windmill_demo.gif");
const legacyEntry = path.join(root, "artifacts", "windmill_demo.html");

await rm(exportDir, { recursive: true, force: true });
await mkdir(exportDir, { recursive: true });
await cp(outDir, exportDir, { recursive: true });
await cp(certificatePath, path.join(exportDir, "sample_certificate.json"));
await cp(gifPath, path.join(exportDir, "windmill_demo.gif"));

const index = await readFile(path.join(exportDir, "index.html"), "utf8");
await writeFile(
  path.join(exportDir, "index.html"),
  index.replaceAll('href="/', 'href="./').replaceAll('src="/', 'src="./'),
  "utf8",
);

await writeFile(
  legacyEntry,
  `<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=./next-demo/index.html">
<title>Windmill Demo Redirect</title>
<body>
  <p>Redirecting to <a href="./next-demo/index.html">the React/Next.js windmill demo</a>.</p>
</body>
</html>
`,
  "utf8",
);
