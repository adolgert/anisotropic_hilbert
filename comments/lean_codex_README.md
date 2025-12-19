## Codex + Lean container

Lean 4.26.0 is preinstalled (via elan) to match `lean/lean-toolchain`. Use this image to run Codex with the project mounted.
Node is installed from the latest stable NodeSource repo.

### Build
```bash
docker build -t anisotropic-codex -f codex/Dockerfile codex
```
Codex CLI (`@openai/codex-cli`) is installed via npm during the build. If you prefer to install it at runtime instead, remove that layer from the Dockerfile and `npm install -g @openai/codex-cli` inside the running container.
If the package is private, pass an npm token at build time:
```bash
docker build \
  --build-arg NPM_TOKEN="$NPM_TOKEN" \
  -t anisotropic-codex \
  -f codex/Dockerfile codex
```

### Run (mount project + tokens)
Minimal (mount workspace and config):
```bash
docker run --rm -it --network host \
  -v "$(pwd)":/workspace \
  -v ~/.config/codex:/home/coder/.config/codex:ro \
  anisotropic-codex
```

With environment variables passed through:
```bash
docker run --rm -it \
  -v "$(pwd)":/workspace \
  -v ~/.config/codex:/home/coder/.config/codex:ro \
  -e OPENAI_API_KEY \
  -e OTHER_TOKEN=... \
  anisotropic-codex
```
- `~/.config/codex` mount lets you reuse your host Codex login; remove it if you prefer to log in anew inside the container.
- To pass extra secrets, add more `-e VAR=value` entries.
- Codex CLI is installed via npm inside the image; if you prefer not to bake it in, remove that layer and install inside the running container instead.

### Authentication options
- **Reuse host login:** keep the `~/.config/codex` bind above (drop `:ro` if the container needs to write updates).
- **Device/browser login from container:** inside the running container run `codex auth login` (or `codex login`), open the printed URL on your host, enter the code, and approve.

### Working in the project
```bash
cd /workspace/lean
lake update
```
From there you can run `codex` in the mounted repo and work on the Lean proofs.
