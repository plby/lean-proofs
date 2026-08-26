// Run from src/latest/. Recheck the local proof dependency closure without
// changing Lean's computational limits or generating Lake setup metadata.
import { readFileSync, readdirSync, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { spawnSync } from 'node:child_process';

const target = 'ErdosProblems.Erdos822';
const proofDir = 'ErdosProblems/Erdos822';
const sourcePath = name => `${name.replaceAll('.', '/')}.lean`;
const forbidden = /\b(?:sorry|admit|axiom|unsafe|opaque)\b|set_option\s+(?:maxHeartbeats|maxRecDepth)/;
const allFiles = [sourcePath(target), ...readdirSync(proofDir)
  .filter(name => name.endsWith('.lean')).map(name => `${proofDir}/${name}`)];
for (const path of allFiles) {
  const lines = readFileSync(path, 'utf8').split('\n');
  for (let i = 0; i < lines.length; ++i) {
    if (forbidden.test(lines[i])) {
      throw new Error(`Forbidden proof placeholder or limit setting: ${path}:${i + 1}`);
    }
  }
}
console.log(`Placeholder/limit scan passed: ${allFiles.length} Lean files.`);

const visited = new Set();
const visiting = new Set();
const order = [];
function visit(name) {
  if (visited.has(name)) return;
  if (visiting.has(name)) throw new Error(`Import cycle at ${name}`);
  visiting.add(name);
  const source = readFileSync(sourcePath(name), 'utf8');
  for (const match of source.matchAll(/^import\s+([A-Za-z0-9_.]+)/gm)) {
    const dep = match[1];
    if (dep === target || dep.startsWith(`${target}.`)) visit(dep);
  }
  visiting.delete(name);
  visited.add(name);
  order.push(name);
}
visit(target);
console.log(`Acyclic local proof closure: ${order.length} modules.`);
for (let i = 0; i < order.length; ++i) {
  const name = order[i];
  const output = `.lake/build/lib/lean/${name.replaceAll('.', '/')}.olean`;
  mkdirSync(dirname(output), { recursive: true });
  console.log(`[${i + 1}/${order.length}] ${name}`);
  const result = spawnSync('lake', ['env', 'lean', sourcePath(name), '-o', output], {
    stdio: 'inherit',
  });
  if (result.error) throw result.error;
  if (result.status !== 0) process.exit(result.status ?? 1);
}
console.log(`PASS: ${order.length} local proof modules rechecked, including the final theorem.`);
