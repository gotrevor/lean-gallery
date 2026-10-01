# Aristotle jobs — St05 Thm 1.3 closed-form induction (lap 2026-06-06 late)

Decomposed the stalled `thm13closed` (e0240fef, failed at 9%) into 4 angles:

- **eo_floor**   `1d42ed39-fc75-47be-8e9a-0eaf87c39c27` — even→odd floor identity (crux), full.
- **eo_ineq**    `785dac71-714b-429e-b9b4-a032304171d8` — real-analysis inequality core (fallback).
- **closed_assembly** `7ac5bbdd-fafe-4a9f-a6aa-0765f377022f` — joint induction GIVEN step_eo/step_oe axioms.
- **closed_full** `7bd9143e-8943-4602-8444-89da2ecec77d` — full thm13_closed from scratch, hints baked.

Math fully verified by hand (see docstrings). Working it locally too (General/Thm13Closed.lean).
