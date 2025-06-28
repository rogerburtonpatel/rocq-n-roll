/* eslint-disable @typescript-eslint/naming-convention */
import "./De.css";
import { useCallback, useEffect, useState } from "react";
import { vscode } from "./utilities/vscode";
import Highlighter from "react-highlight-words";

type Slice = { start: number; end: number };
type SlicedScript = { raw: string; slices: Slice[]; grays: Set<number> };
const empty: SlicedScript = {
  raw: "",
  slices: [],
  grays: new Set(),
};

const DeApp = () => {
  const [proof, setProof] = useState<SlicedScript>(empty);
  const [defs, setDefs] = useState<string[]>([]);
  const [flag, setFlag] = useState<boolean>(true);

  const handleMessage = useCallback(
    (msg: any) => {
      switch (msg.data.command) {
        case "load":
          setProof({
            raw: msg.data.script,
            slices: msg.data.slices,
            grays: new Set(),
          });
          setDefs([]);
          break;
        case "definition":
          setDefs((prevDefs) => [msg.data.def, ...prevDefs]);
      }
    },
    [setProof]
  );

  useEffect(() => {
    window.addEventListener("message", handleMessage);
    return () => {
      window.removeEventListener("message", handleMessage);
    };
  }, [handleMessage]);

  return (
    <main>
      {defs.map((d) => (
        <div className="row">
          <code className="code-font">{d}</code>
        </div>
      ))}
      <div className="row space-below">
        <Selectable
          sscript={proof}
          setGrays={(grays: Set<number>) =>
            setProof((old) => {
              return { ...old, grays: grays };
            })
          }
        />
      </div>
      {flag && (
        <div className="row even">
          <button
            onClick={() => {
              vscode.postMessage({
                command: "transparent",
                selection: window.getSelection().toString(),
              });
            }}
          >
            lookup
          </button>
          <button
            onClick={() => {
              vscode.postMessage({
                command: "deautomate",
                grays: Array.from(proof.grays),
              });
              setFlag(false);
            }}
            title="deautomate"
          >
            deautomate
          </button>
        </div>
      )}
    </main>
  );
};

type SelectableProps = {
  sscript: SlicedScript;
  setGrays: any;
};

const Selectable = ({ sscript, setGrays }: SelectableProps) => {
  function highlight(s: string) {
    return (
      <Highlighter
        highlightClassName="admit"
        searchWords={["admit"]}
        textToHighlight={s}
      />
    );
  }

  const handleSelect = useCallback(
    (deselected: boolean, idx: number) => {
      const newgrays = new Set(sscript.grays);
      if (deselected) {
        newgrays.delete(idx);
      } else {
        newgrays.add(idx);
      }
      setGrays(newgrays);
    },
    [setGrays]
  );

  let linelen = 0;
  const raw = sscript.raw;
  let rendered = [];
  let prevEnd = 0;
  for (const sl of sscript.slices) {
    const idx = sl.start;
    rendered.push(<code>{highlight(raw.slice(prevEnd, idx))}</code>);

    const deselected = sscript.grays.has(idx);
    const color = deselected ? "gray" : "yellow";
    rendered.push(
      <button
        className={color + " tight" + " code-font"}
        onClick={() => handleSelect(deselected, idx)}
      >
        {highlight(raw.slice(idx, sl.end))}
      </button>
    );
    linelen += sl.end - prevEnd;
    if (linelen > 35) {
      rendered.push(<br />);
      linelen = 0;
    }
    prevEnd = sl.end;
  }
  rendered.push(<code>{highlight(raw.slice(prevEnd, raw.length))}</code>);
  return <pre>{rendered}</pre>;
};

export default DeApp;
