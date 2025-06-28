import * as vscode from "vscode";
import { getUri } from "./utilities/getUri";
import { getNonce } from "./utilities/getNonce";
import { parse } from "./parse";
import { unscript, untactic } from "./print";
import { Script, Tactic } from "./syntax";
import { makeOpaque, slice } from "./partial";
import { deautomate } from "./algo";
import { LookupCoqtop, TrialCoqtop } from "./coqtop";

export class Otto {
  async deautomate(editor: vscode.TextEditor, uri: vscode.Uri, path: string) {
    const range = editor.selection;
    const first = editor.document.lineAt(0).range.start;
    const prelude = editor.document.getText(
      new vscode.Range(first, range.start)
    );

    // pretty-print input
    const selection = unscript(parse(editor.document.getText(range)));
    const proof = parse(selection);

    await new TrialCoqtop(path).attempt();
    new DeautomatePanel(prelude, proof, uri, path);
  }
}

function makePanel(uri: vscode.Uri) {
  const panel = vscode.window.createWebviewPanel(
    "coq",
    "otto",
    { preserveFocus: true, viewColumn: 2 },
    {
      enableScripts: true,
      localResourceRoots: [
        vscode.Uri.joinPath(uri, "out"),
        vscode.Uri.joinPath(uri, "otto-ui/build"),
      ],
      retainContextWhenHidden: true,
    }
  );
  panel.webview.html = getWebviewContent(panel.webview, uri);

  // this setup is from VSCoq
  function getWebviewContent(
    webview: vscode.Webview,
    extensionUri: vscode.Uri
  ) {
    const stylesUri = getUri(webview, extensionUri, [
      "otto-ui",
      "build",
      "assets",
      "index.css",
    ]);
    const scriptUri = getUri(webview, extensionUri, [
      "otto-ui",
      "build",
      "assets",
      "index.js",
    ]);

    const nonce = getNonce();

    return `
          <!DOCTYPE html>
          <html lang="en">
            <head>
              <meta charset="UTF-8" />
              <meta name="viewport" content="width=device-width, initial-scale=1.0" />
              <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; script-src 'nonce-${nonce}';">
              <link rel="stylesheet" type="text/css" nonce="${nonce}" href="${stylesUri}">
              <title>otto</title>
            </head>
            <body>
              <div id="root"></div>
              <script type="module" nonce="${nonce}" src="${scriptUri}"></script>
            </body>
          </html>
        `;
  }
  return panel;
}

class DeautomatePanel {
  private panel: vscode.WebviewPanel;

  private prelude: string;
  private proof: Script;
  private env: Map<string, Tactic>;
  private path: string;

  constructor(prelude: string, proof: Script, uri: vscode.Uri, path: string) {
    this.panel = makePanel(uri);
    this.prelude = prelude;
    this.proof = proof;
    this.env = new Map<string, Tactic>();
    this.path = path;

    this.setWebviewListener(this.panel.webview);
  }

  private load() {
    this.panel.webview.postMessage({
      command: "load",
      script: unscript(this.proof),
      slices: slice(this.proof),
    });
  }

  private setWebviewListener(webview: vscode.Webview) {
    webview.onDidReceiveMessage(async (msg: any) => {
      switch (msg.command) {
        case "start":
          this.load();
          break;
        case "deautomate":
          const proof = makeOpaque(this.proof, msg.grays);
          const output = await deautomate(
            this.path,
            this.prelude,
            this.env,
            proof
          );
          this.proof = parse(unscript(output));
          this.load();
          break;
        case "transparent":
          const name = msg.selection;
          const [lhs, rhs] = await new LookupCoqtop(
            this.path,
            this.prelude
          ).lookup(name);
          this.env.set(name, rhs);
          this.panel.webview.postMessage({
            command: "definition",
            def: `${lhs} ${untactic(rhs)}.`,
          });
          break;
      }
    });
  }
}
