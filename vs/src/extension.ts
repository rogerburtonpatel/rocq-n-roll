import * as vscode from "vscode";
import { Otto } from "./panel";

export function activate(context: vscode.ExtensionContext) {
  let disposable = vscode.commands.registerTextEditorCommand(
    "otto.deautomate",
    (editor) => {
      const path: string = vscode.workspace
        .getConfiguration("otto")
        .get("coqtop")!;
      const otto = new Otto();
      otto.deautomate(editor, context.extensionUri, path);
    }
  );

  context.subscriptions.push(disposable);
}

export function deactivate() {}
