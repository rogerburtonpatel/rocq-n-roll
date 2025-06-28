- Be able to record and save the proofs 
- Can you include rest notes? 
- Make use of rhythm 
- Use chords not just single notes - that can help make the dissonance more clear 

- https://jlubin.net/music/
- https://us.metamath.org/
- https://github.com/pitag-ha/cardio-crumble?tab=readme-ov-file
- https://youtu.be/OFWCbGzxofU?si=YKM1ndEsGW1nQJbC
- https://www.youtube.com/watch?v=mqsnqIw--RU
- https://youtu.be/cyW5z-M2yzw?si=nUmB6N0AxA8TZ9u9

- Use frequency, not just midi.  

“One of the biggest implementation annoyances for me was that if you're doing something like deautomation you need to parse proofs into tactic ASTs. For me this involved writing my own very brittle antlr4 parser. I imagine tapping into Rocq's actual parser would have been better, since Rocq's grammar is actually super complicated. I remember coq-serapi (the predecessor of coq-lsp ) had some sort of parsing functionality iirc so that's why I thought it might help, but not sure.

By the way, if you don't care about deautomating failing proofs, Rocq's Info command might get you what you need. It doesn't deautomate semicolons but it does print the underlying tactics used within other tactical expressions.

e.g.
```
Goal 1 + 1 = 2.
Proof. 
  Info 0 simpl; try solve [apply I | reflexivity].
will output
simpl;<coq-core.plugins.ltac::reflexivity@0>
```

`vs` folder has Jessica's implementation code of the proof deautomation extension.
