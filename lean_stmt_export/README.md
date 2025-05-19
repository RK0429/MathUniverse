# lean_stmt_export

[![Build Status](https://github.com/RK0429/lean_stmt_export/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/RK0429/lean_stmt_export/actions) [![Lean Version](https://img.shields.io/badge/lean-4.19.0-blue.svg?style=flat-square)](https://leanprover.github.io/) [![License: Apache-2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg?style=flat-square)](https://opensource.org/licenses/Apache-2.0)

## Overview

`lean_stmt_export` is a utility for Lean 4 projects that extracts information about all declarations (definitions, theorems, axioms, inductive types, etc.) and their dependencies from a given Lean file. It also captures dependencies of custom `example` commands. The output is a structured JSON, suitable for further analysis, documentation generation, or visualization of the project's structure. This tool helps in understanding the relationships between different parts of a Lean codebase.

## Features

- Extracts definitions, theorems, axioms, inductive types, and other declarations along with their dependencies.
- Captures dependencies for custom `example` commands in Lean code.
- Outputs structured JSON for both declarations and examples.
- Usable via CLI (`lake exe lean_stmt_export`) and within Lean code (`export_deps` command`).

## Table of Contents

- [lean\_stmt\_export](#lean_stmt_export)
  - [Overview](#overview)
  - [Features](#features)
  - [Table of Contents](#table-of-contents)
  - [Installation](#installation)
  - [Usage](#usage)
  - [Output Format](#output-format)
  - [Contributing](#contributing)
  - [License](#license)

## Installation

To use `lean_stmt_export`, ensure you have Lean 4 (v4.19.0) and Lake installed:

1. **Install Lean 4**: Follow the instructions at [https://leanprover.github.io/lean4/doc/setup.html](https://leanprover.github.io/lean4/doc/setup.html).
2. **Install Lake** (if not already installed):

   ```sh
   elan toolchain install leanprover/lean4:v4.19.0
   ```

3. **Add as a dependency**: In your `lakefile.lean`, add:

   ```lean
   require lean_stmt_export from git "https://github.com/RK0429/lean_stmt_export" @ "main"
   ```

4. **Build your project**:

   ```sh
   lake build
   ```

5. **(Optional)** Install the executable locally:

   ```sh
   lake exe install lean_stmt_export
   ```

## Usage

The primary way to use `lean_stmt_export` is via its main executable.

**Command-Line Interface:**

```sh
lake exe lean_stmt_export <path_to_target_project_root> <path_to_lean_file_to_process>
```

For example, to analyze a file named `MyProject/MyFile.lean`:

```sh
lake exe lean_stmt_export MyProject MyProject/MyFile.lean
```

This will elaborate the specified Lean file and print a JSON object to standard output containing all declarations and captured examples with their dependencies.

**In-Code Usage (for `export_deps` command):**
You can also use the `export_deps` command directly within a Lean file if you have `LeanStmtExport.ExportDeps` imported.

```lean
import LeanStmtExport.ExportDeps

-- ... your Lean code ...

-- This command will print the JSON output to stdout during elaboration
export_deps
```

**Capturing Examples:**
To capture dependencies of specific examples, use the custom `example` command provided by `LeanStmtExport.ExampleCapture`.

```lean
import LeanStmtExport.ExampleCapture

-- This will be captured along with its dependencies
example Nat.add_comm -- or any term
```

## Output Format

The output is a single JSON object with two main keys: `declarations` and `examples`.

```json
{
  "declarations": [
    {
      "name": "MyProject.myDef",
      "kind": "def",
      "deps": ["Math.Add.add", "MyProject.otherDef"]
    }
    // ...
  ],
  "examples": [
    {
      "name": "example_1",
      "deps": ["Nat.add_comm"]
    }
    // ...
  ]
}
```

- **`declarations`**: An array of objects, where each object represents a declaration found in the environment after elaborating the input file.
  - `name`: The fully qualified name of the declaration.
  - `kind`: A string indicating the type of declaration (e.g., `"def"`, `"theorem"`, `"axiom"`).
  - `deps`: A list of fully qualified names of constants that this declaration depends on (found in its type and/or value).
- **`examples`**: An array of objects, where each object represents an example captured using the custom `example` command.
  - `name`: An auto-generated unique name for the example.
  - `deps`: A list of fully qualified names of constants that this example depends on.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on contributing, or open issues and pull requests via GitHub.

## License

Apache License 2.0 (SPDX: Apache-2.0)

This project is licensed under the Apache License 2.0, permitting use, modification, and distribution under the terms of the license. See the [LICENSE](LICENSE) file for full details.
