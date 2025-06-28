"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Otto = void 0;
const vscode = require("vscode");
const getUri_1 = require("./utilities/getUri");
const getNonce_1 = require("./utilities/getNonce");
const parse_1 = require("./parse");
const print_1 = require("./print");
const partial_1 = require("./partial");
const algo_1 = require("./algo");
const coqtop_1 = require("./coqtop");
class Otto {
    async deautomate(editor, uri, path) {
        const range = editor.selection;
        const first = editor.document.lineAt(0).range.start;
        const prelude = editor.document.getText(new vscode.Range(first, range.start));
        // pretty-print input
        const selection = (0, print_1.unscript)((0, parse_1.parse)(editor.document.getText(range)));
        const proof = (0, parse_1.parse)(selection);
        await new coqtop_1.TrialCoqtop(path).attempt();
        new DeautomatePanel(prelude, proof, uri, path);
    }
}
exports.Otto = Otto;
function makePanel(uri) {
    const panel = vscode.window.createWebviewPanel("coq", "otto", { preserveFocus: true, viewColumn: 2 }, {
        enableScripts: true,
        localResourceRoots: [
            vscode.Uri.joinPath(uri, "out"),
            vscode.Uri.joinPath(uri, "otto-ui/build"),
        ],
        retainContextWhenHidden: true,
    });
    panel.webview.html = getWebviewContent(panel.webview, uri);
    // this setup is from VSCoq
    function getWebviewContent(webview, extensionUri) {
        const stylesUri = (0, getUri_1.getUri)(webview, extensionUri, [
            "otto-ui",
            "build",
            "assets",
            "index.css",
        ]);
        const scriptUri = (0, getUri_1.getUri)(webview, extensionUri, [
            "otto-ui",
            "build",
            "assets",
            "index.js",
        ]);
        const nonce = (0, getNonce_1.getNonce)();
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
    panel;
    prelude;
    proof;
    env;
    path;
    constructor(prelude, proof, uri, path) {
        this.panel = makePanel(uri);
        this.prelude = prelude;
        this.proof = proof;
        this.env = new Map();
        this.path = path;
        this.setWebviewListener(this.panel.webview);
    }
    load() {
        this.panel.webview.postMessage({
            command: "load",
            script: (0, print_1.unscript)(this.proof),
            slices: (0, partial_1.slice)(this.proof),
        });
    }
    setWebviewListener(webview) {
        webview.onDidReceiveMessage(async (msg) => {
            switch (msg.command) {
                case "start":
                    this.load();
                    break;
                case "deautomate":
                    const proof = (0, partial_1.makeOpaque)(this.proof, msg.grays);
                    const output = await (0, algo_1.deautomate)(this.path, this.prelude, this.env, proof);
                    this.proof = (0, parse_1.parse)((0, print_1.unscript)(output));
                    this.load();
                    break;
                case "transparent":
                    const name = msg.selection;
                    const [lhs, rhs] = await new coqtop_1.LookupCoqtop(this.path, this.prelude).lookup(name);
                    this.env.set(name, rhs);
                    this.panel.webview.postMessage({
                        command: "definition",
                        def: `${lhs} ${(0, print_1.untactic)(rhs)}.`,
                    });
                    break;
            }
        });
    }
}
//# sourceMappingURL=panel.js.map