# lean_stmt_export

[![Lean Version](https://img.shields.io/badge/lean-4-blue.svg?style=flat-square)](https://leanprover.github.io/) [![License: Apache-2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg?style=flat-square)](https://opensource.org/licenses/Apache-2.0)

## Overview

`lean_stmt_export` is a utility for Lean 4 projects that extracts information about all declarations (definitions, theorems, axioms, inductive types, etc.) and their dependencies from a given Lean file. It also captures dependencies of custom `example` commands. The output is a structured JSON, suitable for further analysis, documentation generation, or visualization of the project's structure. This tool helps in understanding the relationships between different parts of a Lean codebase.

## Table of Contents

- [lean\_stmt\_export](#lean_stmt_export)
  - [Overview](#overview)
  - [Table of Contents](#table-of-contents)
  - [Installation](#installation)
  - [Usage](#usage)
  - [Output Format](#output-format)
  - [Contributing](#contributing)
  - [License](#license)

## Installation

1. **Ensure Lean 4 is installed:** Follow the instructions on the [official Lean website](https://leanprover.github.io/lean4/doc/setup.html).
2. **Add `lean_stmt_export` as a dependency:**
    In your `lakefile.lean`, add:

    ```lean
    require lean_stmt_export from git "https://github.com/RK0429/lean_stmt_export" @ "main"
    ```

    (Replace `"https://github.com/RK0429/lean_stmt_export"` with the actual repository URL if it's hosted elsewhere.)
3. **Build your project:**
    Run `lake build` in your project's root directory.

## Usage

The primary way to use `lean_stmt_export` is via its main executable.

**Command-Line Interface:**

```sh
lake exe lean_stmt_export <path_to_your_lean_file.lean>
```

For example, to analyze a file named `MyProject/MyFile.lean`:

```sh
lake exe lean_stmt_export MyProject/MyFile.lean
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
      "name": "MyProject.myDefinition",
      "kind": "def", // or "theorem", "axiom", "inductive", "opaque", "other"
      "deps": ["Dependency1.name", "Dependency2.name"]
    }
    // ... more declarations
  ],
  "examples": [
    {
      "name": "example_123", // auto-generated unique name
      "deps": ["ExampleDependency1.name", "ExampleDependency2.name"]
    }
    // ... more captured examples
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

Contributions are welcome! Please feel free to open an issue or submit a pull request.
When contributing, please ensure your code adheres to the existing style and that any new functionality is appropriately covered by tests (if applicable).

(Link to `CONTRIBUTING.md` would go here if it existed in the project)

## License

This project is licensed under the Apache License 2.0.
SPDX-Identifier: Apache-2.0
See the [LICENSE](LICENSE) file for details (if a LICENSE file exists).
