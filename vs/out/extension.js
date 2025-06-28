"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = require("vscode");
const panel_1 = require("./panel");
function activate(context) {
    let disposable = vscode.commands.registerTextEditorCommand("otto.deautomate", (editor) => {
        const path = vscode.workspace
            .getConfiguration("otto")
            .get("coqtop");
        const otto = new panel_1.Otto();
        otto.deautomate(editor, context.extensionUri, path);
    });
    context.subscriptions.push(disposable);
}
function deactivate() { }
//# sourceMappingURL=extension.js.map