# Braindump

## The Types

Full pipeline: 

### Program 1: `rocq2midi`

#### Module 1 : `hooks` (Ocaml hooks into Rocq over ltac) :
`keystroke` -> `ltac_step` 

There are two ways for `hooks` to work: 
1. As a concurrently-running program with the ROCQ compiler (ROCQC), or 
2. Through the Language Server Protocol (LSP), ideally, or at least emacs' Proof
General (PG). 

The latter allows for interactive stepping, which we as musicians would likely
prefer. 

- Stepping through a proof within the program the program produces a stream of
"`ltac_step`" (this is my placeholder name for whatever type LSP or PG gives
us). 
- If we're in the compiler, we get the entire stream all at once. We will
  naturally need to introduce temporal delay between steps, or all the sounds
  will be played in an instant, which will be ugly. 

#### Module 2 : `step_2_midi` :
 `ltac_step` -> `MIDI`

This is a *module* in the same *program* as `hooks` (`rocq2midi`). It takes the `ltac_step`s produced by `hooks` and produces MIDI over a channel, 
concurrent with either the execution of ROCQC or simply as a byproduct of 
LSP/PG. 

### Program 2 :`synth` (Synthesizer) :

`MIDI` -> sound

`synth` runs concurrently in the background at all times. It "knows" what MIDI
channel to listen on, and will play programmed sound when receiving MIDI input
on that channel. 

Programming the synth to decide what sound to produce, and
orchestrating that sound via what kind of MIDI `step_to_midi` produces, is the
fun musical part. 


## Program execution 

1. A program, either LSP, PG, or ROCQC, steps through a Rocq proof. 
2. Our attached program*, `rocq2midi`, intercepts the hooks* produced by stepping through the program, and produces a stream of MIDI on Channel `N` (the value of `N` does not really matter, at all). 
3. Concurrently, `synth` reads MIDI on Channel `N` and produces sound. 

## *The Challenge

The hard part is determining what 'attached to the program' and 'intercepting
the hooks' really means. Do we fork ROCQC? Do we fork LSP/PG? Is there an easy
way to build software on top of these that doesn't involve recompilation? These
are questions to answer together. 



### 5.11
1. FluidSynth or productive alternative 
2. Ambient tone- run at start of program. 
  - Envelope: 0 Attack for slow startup, 0 decay, inf. sustain until MIDI stop,
    gentle release. 
2. Pulsing beat. Simple, understated but with presence. 
3. Comments are lightly tonal, perhaps altering the shape of the ambient tone? 
4. Imports, functions similar for now. 
5. Proofs are the meat. 

TODO: 
- [x] Install Fluidsynth (FS), get it working
- [x] Research MIDI generation options: **Using Portmidi**
- [ ] Set up PortMidi infrastructure 
- [ ] Cook up some good Fluidsynth (FS) soundfonts
- [ ] (Maybe): Use Garageband instead? A GUI is nice here for collaboration and
soundfont building. 
- [ ] Module to 
  1. spawn FS w/ configuration:
    - soundfont(s), 
    - default initialization of the synth, 
    - audio driver 
  
  (Do this with a config file or CL args)

  2. inject ambience and rhythm 
- [ ] Sound library for 
  - comments 
  - non-proof code
  - proofs 
