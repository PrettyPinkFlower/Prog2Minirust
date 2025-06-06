import outdent from "outdent";
import * as Types from "vscode-languageserver-types";
import * as LanguageServer from "./../src/LanguageServer";

describe("ocamllsp/hoverExtended", () => {
  let languageServer: LanguageServer.LanguageServer;

  afterEach(async () => {
    await LanguageServer.exit(languageServer);
  });

  it("returns type inferred under cursor", async () => {
    languageServer = await LanguageServer.startAndInitialize();
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        "let x = 1\n",
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(0, 4),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "int",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 0,
    },
    "start": {
      "character": 4,
      "line": 0,
    },
  },
}
`);
  });

  it("returns type inferred under cursor (markdown formatting)", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        "let x = 1\n",
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(0, 4),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
int
\`\`\`",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 0,
    },
    "start": {
      "character": 4,
      "line": 0,
    },
  },
}
`);
  });

  it("returns type inferred under cursor with documentation", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
        (** This function has a nice documentation *)
        let id x = x

        let () = id ()
        `,
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(3, 9),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
'a -> 'a
\`\`\`
***
This function has a nice documentation",
  },
  "range": {
    "end": {
      "character": 11,
      "line": 3,
    },
    "start": {
      "character": 9,
      "line": 3,
    },
  },
}
`);
  });

  it("returns type inferred under cursor with documentation with tags (markdown formatting)", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
        (** This function has a nice documentation.

            It performs division of two integer numbers.

            @param x dividend
            @param divisor

            @return {i quotient}, i.e. result of division
            @raise Division_by_zero raised when divided by zero

            @see <https://en.wikipedia.org/wiki/Arithmetic#Division_(%C3%B7,_or_/)> article
            @see 'arithmetic.ml' for more context

            @since 4.0.0
            @before 4.4.0

            @deprecated use [(/)]

            @version 1.0.0
            @author John Doe *)
        let div x y =
          x / y

        let f = div 4 2
        `,
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(23, 10),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
int -> int -> int
\`\`\`
***
This function has a nice documentation.

It performs division of two integer numbers.

***@param*** \`x\`
dividend

***@param*** divisor

***@return***
*quotient*, i.e. result of division

***@raise*** \`Division_by_zero\`
raised when divided by zero

***@see*** [link](https://en.wikipedia.org/wiki/Arithmetic#Division_\\(%C3%B7,_or_/\\))
article

***@see*** \`arithmetic.ml\`
for more context

***@since*** \`4.0.0\`

***@before*** \`4.4.0\`

***@deprecated***
use \`(/)\`

***@version*** \`1.0.0\`

***@author*** John Doe",
  },
  "range": {
    "end": {
      "character": 11,
      "line": 23,
    },
    "start": {
      "character": 8,
      "line": 23,
    },
  },
}
`);
  });

  it("returns good type when cursor is between values", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
          let f i f = float_of_int i +. f
          let i = 10
          let f = 10.
          let sum = f i f
       `,
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(3, 13),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
int
\`\`\`",
  },
  "range": {
    "end": {
      "character": 13,
      "line": 3,
    },
    "start": {
      "character": 12,
      "line": 3,
    },
  },
}
`);
  });

  it("regression test for #343", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
          type t = s
          and s = string
          type 'a fib = ('a -> unit) -> unit
       `,
      ),
    });

    const hover1 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(1, 4),
      verbosity: 0,
    });

    expect(hover1).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
type s = t
\`\`\`",
  },
  "range": {
    "end": {
      "character": 14,
      "line": 1,
    },
    "start": {
      "character": 0,
      "line": 1,
    },
  },
}
`);

    const hover2 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 9),
      verbosity: 0,
    });

    expect(hover2).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
type 'a fib = ('a -> unit) -> unit
\`\`\`",
  },
  "range": {
    "end": {
      "character": 34,
      "line": 2,
    },
    "start": {
      "character": 0,
      "line": 2,
    },
  },
}
`);
  });

  it("regression test for #403", async () => {
    languageServer = await LanguageServer.startAndInitialize();
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
type foo = int

let x : foo = 1
`,
      ),
    });

    const result = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
      verbosity: 0,
    });

    expect(result).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "foo",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);
  });

  it("FIXME: reproduce [#344](https://github.com/ocaml/ocaml-lsp/issues/344)", async () => {
    languageServer = await LanguageServer.startAndInitialize({
      capabilities: {
        textDocument: {
          hover: {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"],
          },
          moniker: {},
        },
      },
    });

    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        // the empty space below is necessary to reproduce the bug
        outdent`
























        let k = ()
        let m = List.map
        `,
      ),
    });

    // here we see that all is ok
    const hoverOverK = await languageServer.sendRequest(
      "ocamllsp/hoverExtended",
      {
        textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
        position: Types.Position.create(24, 4),
        verbosity: 0,
      },
    );

    expect(hoverOverK).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
unit
\`\`\`",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 24,
    },
    "start": {
      "character": 4,
      "line": 24,
    },
  },
}
`);

    // we trigger the bug
    const autocompleteForListm = await languageServer.sendRequest(
      "ocamllsp/hoverExtended",
      {
        textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
        position: Types.Position.create(25, 15),
        verbosity: 0,
      },
    );

    const buggedHoverOverK = await languageServer.sendRequest(
      "ocamllsp/hoverExtended",
      {
        textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
        position: Types.Position.create(24, 4),
        verbosity: 0,
      },
    );

    // now the same hover as before comes with unrelated documentation
    expect(buggedHoverOverK).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "markdown",
    "value": "\`\`\`ocaml
unit
\`\`\`",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 24,
    },
    "start": {
      "character": 4,
      "line": 24,
    },
  },
}
`);
  });

  it("supports explicity verbosity", async () => {
    languageServer = await LanguageServer.startAndInitialize();
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
type foo = int option

let x : foo = Some 1
        `,
      ),
    });

    const result0 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
      verbosity: 0,
    });

    expect(result0).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "foo",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);

    const result1 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
      verbosity: 1,
    });

    expect(result1).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "int option",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);

    const result2 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
      verbosity: 2,
    });

    expect(result2).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "int option",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);
  });

  it("supports implicit verbosity", async () => {
    languageServer = await LanguageServer.startAndInitialize();
    await languageServer.sendNotification("textDocument/didOpen", {
      textDocument: Types.TextDocumentItem.create(
        "file:///test.ml",
        "ocaml",
        0,
        outdent`
type foo = int option

let x : foo = Some 1
        `,
      ),
    });

    const result0 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
    });

    expect(result0).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "foo",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);

    const result1 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
    });

    expect(result1).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "int option",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);

    const result2 = await languageServer.sendRequest("ocamllsp/hoverExtended", {
      textDocument: Types.TextDocumentIdentifier.create("file:///test.ml"),
      position: Types.Position.create(2, 4),
    });

    expect(result2).toMatchInlineSnapshot(`
{
  "contents": {
    "kind": "plaintext",
    "value": "int option",
  },
  "range": {
    "end": {
      "character": 5,
      "line": 2,
    },
    "start": {
      "character": 4,
      "line": 2,
    },
  },
}
`);
  });
});
