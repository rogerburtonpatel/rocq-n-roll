# Implementation

We wrote a proof-of-concept implementation of deautomation as a VS Code
extension. We focused on simple (but brittle) instantiations that allowed us to
rapidly see how deautomation works on small examples and experiment with
different features. In the future, to move past this proof-of-concept stage, we
will develop a tool that works more broadly and more robustly.

We used VSCoq as a reference to learn how to structure an extension
and as a source of some utility functions.

## Examples from Theory: Basics

To follow along, please see `BasicsExample.mov` in the `ts/examples` folder.
These correspond to the two examples in the Theory: Basics section of the paper.

After selecting the first proof and opening the deautomation panel, we can see
from the yellow highlights how the automation constructs are being parsed.
Clicking "deautomate" will rid the proof of these constructions.

Close out of the panel, select the second proof, and run the same steps.
Now, the deatuomated proof will indicate where and why a failure occurred.

## Example from Introduction

To follow along, please see `IntroExample.mov` Deautomating the (broken) proof
of `bevalR_implies_beval` corresponds to the example in the Introduction section
of the paper.

## (Small) Examples of Experimental Features

To follow along, please see `ExperimentalExamples.mov`.

In the first proof, we demonstrate a small example of partial deautomation: when
`auto` is highlighted yellow, it will be deautomated; when it is deselcted and
highlighed gray, it will not be deautomated.

In the second proof, we demonstrate a small example of deautomating custom
tactics: we select the custom tactic `veryeasy` and use the "lookup" button to
show its definition, which will now be inlined when deautomating.

## Running the Extension Locally

Since this implementation is proof-of-concept, we have not extensively tested
the process of installing and running the extension on devices other than our
own. Instead, we made sure to provide screen capture videos for the examples
above. If you would still like to try running things locally:

The extension needs to be run through VS Code. We use version 1.87.1.

We use package manager `npm` for our TypeScript project. Within the `ts` folder,
run
```
$ npm run install:all
$ npm run build:all
$ npm run compile
```

Open the `ts` folder within VS Code. Go to `src/extension.ts` and run `F5` to
start the extension. The extension runs `coqtop`, which you may need to provide
a path for. to do this, go to `Preferences: Open Workspace Settings`, search for
`Otto: Coqtop`, and replace the path as needed.

Navigate to the `ts/examples` folder containing the examples.

Select the proof you want to deautomate by highlighting the entire proof,
starting from (but not including) the "Proof." Through the command palette, run
the "Open Deautomation Panel" command. This should open a side panel containing
the selected proof. Click the "deautomate" button in the panel to view the
deautomation of the script.