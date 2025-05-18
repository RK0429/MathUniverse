# Implementation Checklist

Before diving into the lists, here's the big picture: you'll stand up **two tightly-coupled workspaces**—Lean 4 (with `lake`) and Rust—wire them to a Docusaurus site, and then automate everything so that *saving* a `.lean` file locally or *pushing* to `main` in GitHub instantly regenerates MDX, rebuilds the site, and redeploys it. Below, each section expands the original checklist with extra context, commands, and file snippets.

---

## 1 · Repository & Tool-chain Bootstrap

* [ ] **Create the monorepo** (e.g. `mathuniverse/`) with two top-level dirs: `lean/` and `mdx-gen/` (Rust).
* [ ] **Install Lean 4 + `lake`** via `elan`, verify with `lake -h`. ([GitHub][1])
* [ ] **Add `lean_stmt_export` executable** in `lean/lakefile.toml`; expose `main` that calls the necessary Lean functions to generate `stmt_deps.json` as described in `design/lean-parser.md`. ([Leanコミュニティ][2], `design/lean-parser.md`)
* [ ] **Install the Rust tool-chain** (`rustup toolchain install stable`), then `cargo new mdx-gen --bin`.
* [ ] **Add Rust dependencies** in `mdx-gen/Cargo.toml`:

  ```toml
  [dependencies]
  serde = { version = "1", features = ["derive"] }
  serde_json = "1"
  # tree-sitter = "0.22"           # Removed: No longer needed for example parsing
  # tree-sitter-lean = "0.1"      # Removed: Grammar crate not needed by mdx-gen
  tera = "1"                   # or handlebars = "5"
  clap = { version = "4", features = ["derive"] }
  ```

  *Tera* and *Handlebars* are both mature; pick one. ([Keats][3], [GitHub][4])
* [ ] **Initial commit** (`git init`, push to GitHub).

---

## 2 · Local "Save → Rebuild" Automation

### 2.1 VS Code tasks

1. **Open `.vscode/tasks.json`** and add:

   ```jsonc
   {
     "version": "2.0.0",
     "tasks": [
       {
         "label": "Lean → stmt_deps.json",
         "type": "shell",
         "command": "lake exe lean_stmt_export",
         "options": {
           "cwd": "${workspaceFolder}/lean" // Assuming lean_stmt_export runs from the lean directory
         },
         "problemMatcher": [],
         "runOptions": { "runOn": "fileSave" }   // triggers on save
       },
       {
         "label": "stmt_deps.json → MDX",
         "type": "shell",
         "command": "cargo run -p mdx-gen -- --input lean/stmt_deps.json --out-dir docs/formal", // Adjust paths as needed
         "options": {
           "cwd": "${workspaceFolder}/mdx-gen" // Assuming mdx-gen runs from its directory
         },
         "dependsOn": ["Lean → stmt_deps.json"],
         "runOptions": { "runOn": "fileSave" }
       }
     ]
   }
   ```

   `runOn:"fileSave"` is documented in VS Code's tasks API. ([Visual Studio Code][5])

2. **Enable format-on-save** for JSON/MDX if desired (`editor.formatOnSave`).

### 2.2 Rust binary (`mdx-gen`)

* **Parse arguments** with *clap* (`--input <path_to_stmt_deps.json>`, `--out-dir <output_directory_for_mdx>`).
* **Deserialize `stmt_deps.json`** with Serde (this file now contains all declarations, including examples, as per `design/lean-parser.md`).
* **Render MDX**: load templates (`templates/theorem.mdx`, `templates/definition.mdx`, etc.) via Tera/Handlebars using the data from `stmt_deps.json` and write to the specified output directory (e.g., `docs/formal/`).
* **Return non-zero exit code** on any serialization/IO error so CI fails early.

---

## 3 · Static-Site Generation (Docusaurus)

* [ ] **Scaffold site**: `npm create docusaurus@latest docs classic`. ([Schema.org][7])
* [ ] **Add math support**:

  ```js
  presets: [
    [
      'classic',
      { remarkPlugins: [require('remark-math')], rehypePlugins: [require('rehype-katex')] }
    ]
  ]
  ```

* [ ] **Add GraphView plugin** (`npm i @arsero/docusaurus-graph`) and update `docusaurus.config.js`:

  ````js
  themes: ['@docusaurus/theme-classic', '@arsero/docusaurus-graph'],
  graph: { contentPath: 'docs/formal' }
  ``` :contentReference[oaicite:6]{index=6}  
  ````

* [ ] **Copy `<LeanPlayground>` component** from *lean4web* (or install via `npm i lean4web`). ([GitHub][8])
* [ ] **Place generated MDX** under `docs/formal/`; Docusaurus auto-discovers.

---

## 4 · Interactive & Discovery Features

### 4.1 Lean playground widgets

Insert in every template:

```mdx
import LeanPlayground from '@site/src/components/LeanPlayground';

<LeanPlayground code={`theorem foo : ... := by`} />
```

The component opens an iframe to a Lean server (self-host or use live.lean-lang.org). ([GitHub][8])

### 4.2 Graph view

`npx docusaurus build` now includes a "Graph" tab that visualises backlinks and prerequisites. ([GitHub][9])

### 4.3 Algolia DocSearch

* **Apply** via the OSS form; Algolia emails you `appId`, `apiKey`, `indexName`. ([docsearch.algolia.com][10])
* **Add to config**:

  ```js
  themeConfig: {
    algolia: {
      appId: 'XXX',
      apiKey: 'YYY',
      indexName: 'ZZZ'
    }
  }
  ```

Crawler auto-indexes each deploy.

---

## 5 · CI / CD Pipeline (GitHub Actions)

```yaml
name: docs
on: [push]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-node@v4
        with: { node-version: 20 }

      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with: { toolchain: stable, override: true }

      - name: Cache elan
        uses: actions/cache@v4
        with:
          path: ~/.elan
          key: ${{ runner.os }}-elan-${{ hashFiles('lean/lean-toolchain') }}
      - run: lake exe lean_stmt_export      # Lean: generates stmt_deps.json in lean/stmt_deps.json
        working-directory: ./lean # Assuming lean_stmt_export is run from the lean directory
      - run: cargo run -p mdx-gen -- --input lean/stmt_deps.json --out-dir docs/formal # Rust: processes stmt_deps.json
        working-directory: ./mdx-gen # Assuming mdx-gen is run from its directory and paths are relative or absolute
      - run: npm ci && npm run build
      - name: Deploy
        uses: peaceiris/actions-gh-pages@v4
        with: { github_token: ${{ secrets.GITHUB_TOKEN }}, publish_dir: ./build }
```

*`peaceiris/actions-gh-pages`* is the most common single-step deploy. ([GitHub][11])
The Lean community suggests caching `elan` to cut mathlib rebuild time. ([GitHub][12])

---

## 6 · Security Hardening

* **Wrap any server-side Lean instances** (required for heavy proofs) in `bubblewrap` to drop privileges and mount a minimal filesystem. ([GitHub][13])
* **Limit outbound network** with `--unshare-net` if proofs don't need it.
* **Set CORS** and isolate the `/playground` route behind rate-limit middleware.

---

## 7 · Metadata & SEO

* **Inject JSON-LD** for each page, aligned with `schema.org/ScholarlyArticle` as shown in `design/idea.md`:

  ````json
  {
    "@context": "https://schema.org",
    "@type": "ScholarlyArticle",
    "identifier": "{{id}}",                           // e.g., van_der_waerden
    "name": "{{name}}",                             // e.g., Van der Waerden's theorem
    "genre": "{{category}}",                        // e.g., Pure mathematics (from YAML front-matter)
    "keywords": ["{{field}}", "{{subfield}}"],       // e.g., ["Discrete Mathematics & Combinatorics", "Ramsey theory"]
    "version": "{{git_sha}}",                       // e.g., ab12c34
    "isBasedOn": "{{repo_url}}/tree/{{git_sha}}",   // URL to the specific commit in the repo
    "url": "{{site_url}}/{{type}}/{{id}}",          // Permanent link to the page
    "description": "{{page_description_or_abstract}}", // A brief description of the content
    "provider": {
      "@type": "Organization",
      "name": "MathUniverse" // Or your project's name
    }
    // Add other relevant fields like `author`, `datePublished`, `license` as available
  }
  ````

* **Add `SitemapPlugin`** in Docusaurus for crawler friendliness (`npm i @docusaurus/plugin-sitemap`).

---

## 8 · Contributor Experience

* [ ] **Write `CONTRIBUTING.md`** covering: branching (`feature/*`, `main`), pre-commit (`lake build`, `cargo check`, `npm run build:mdx`), and how preview URLs are posted by CI.
* [ ] **Add GitHub issue templates** for "new theorem" & "bug report".
* [ ] **Enable Dependabot** for `Cargo.toml`, `package.json`, and GitHub Actions.

---

## 9 · Milestones & Releases

| Version  | Target                                            | Success Criteria                                   |
| -------- | ------------------------------------------------- | -------------------------------------------------- |
| **v1.0** | End-to-end save-to-deploy pipeline working        | Any `.lean` edit appears on prod site within 2 min |
| **v1.1** | Public GraphQL/REST endpoint for theorem metadata | `GET /api/theorem/{id}` returns JSON               |
| **v1.2** | Obsidian vault exporter                           | `.zip` downloads with MD/JSONLD & backlinks        |
| **v1.3** | Citation graph overlay (Crossref enrichment)      | Hovering a DOI shows forward/backward citations    |

---

[1]: https://github.com/leanprover/lean4/blob/master/src/lake/README.md?utm_source=chatgpt.com "lean4/src/lake/README.md at master - GitHub"
[2]: https://leanprover-community.github.io/con-nf/doc/Lake/Config/Package.html?utm_source=chatgpt.com "Lake.Config.Package - Lean community"
[3]: https://keats.github.io/tera/docs/?utm_source=chatgpt.com "Tera - GitHub Pages"
[4]: https://github.com/sunng87/handlebars-rust?utm_source=chatgpt.com "GitHub - sunng87/handlebars-rust: Rust templating with ..."
[5]: https://code.visualstudio.com/api/references/vscode-api?utm_source=chatgpt.com "VS Code API | Visual Studio Code Extension API"
[6]: https://crates.io/crates/tree-sitter-cooklang?utm_source=chatgpt.com "tree-sitter-cooklang - crates.io: Rust Package Registry"
[7]: https://schema.org/ScholarlyArticle?utm_source=chatgpt.com "ScholarlyArticle - Schema.org Type"
[8]: https://github.com/leanprover-community/lean4web?utm_source=chatgpt.com "leanprover-community/lean4web: The Lean 4 web editor - GitHub"
[9]: https://github.com/Arsero/docusaurus-graph?utm_source=chatgpt.com "Arsero/docusaurus-graph - GitHub"
[10]: https://docsearch.algolia.com/?utm_source=chatgpt.com "DocSearch: Search made for documentation | DocSearch by Algolia"
[11]: https://github.com/peaceiris/actions-gh-pages?utm_source=chatgpt.com "peaceiris/actions-gh-pages - GitHub"
[12]: https://github.com/leanprover/lean4/issues/3950?utm_source=chatgpt.com "Create a standard GitHub action for Lean projects · Issue #3950"
[13]: https://github.com/containers/bubblewrap?utm_source=chatgpt.com "containers/bubblewrap: Low-level unprivileged sandboxing ... - GitHub"
