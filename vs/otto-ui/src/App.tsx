/* eslint-disable @typescript-eslint/naming-convention */

import DeApp from "./De";
import { vscode } from "./utilities/vscode";

const App = () => {
  vscode.postMessage({ command: "start" });
  return (
    <div>
      <DeApp />
    </div>
  );
};

export default App;
