---- MODULE NondeterministicAssignment ----

EXTENDS Integers, Sequences, TLC, FiniteSets

\* #include NondeterministicAssignment.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _globalsScratch, _ret, _actor, map
vars == <<_pc, _frames, _globalsScratch, _ret, _actor, map>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_begin">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _globalsScratch = _Undefined
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ map = (<<>>)
_halt(self) ==
  /\ (_actor = self)
  /\ (_pc[self] = <<>>)
  /\ LET _tmp == _Undefined IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = <<>>] IN
        /\ LET _tmp_3 == _globalsScratch["map"] IN
          /\ LET _tmp_4 == _Undefined IN
            /\ _actor' = _tmp
            /\ _frames' = _tmp_2
            /\ _globalsScratch' = _tmp_4
            /\ _ret' = _tmp_1
            /\ map' = _tmp_3
            /\ UNCHANGED _pc
_begin_main(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_5 == self IN
    /\ (self \in main_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00005_pick">>)] IN
      /\ LET _tmp_7 == [map |-> map] IN
        /\ _actor' = _tmp_5
        /\ _globalsScratch' = _tmp_7
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED map
_main_line00005_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00005_pick")
  /\ (_actor = self)
  /\ \E _tmp_8 \in {0}:
    /\ LET _tmp_9 == _tmp_8 IN
      /\ LET _tmp_10 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("x" :> _tmp_9) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_11 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00006_pick">>)] IN
          /\ _frames' = _tmp_10
          /\ _pc' = _tmp_11
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED map
_main_line00006_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00006_pick")
  /\ (_actor = self)
  /\ \E _tmp_12 \in {1, 2, 3}:
    /\ LET _tmp_13 == _tmp_12 IN
      /\ LET _tmp_14 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("x" :> _tmp_13) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ (_tmp_14[self][Len(_tmp_14[self])].x > 1)
        /\ LET _tmp_15 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00007_pick">>)] IN
          /\ _frames' = _tmp_14
          /\ _pc' = _tmp_15
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED map
_main_line00007_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00007_pick")
  /\ (_actor = self)
  /\ \E _tmp_16 \in {TRUE}:
    /\ LET _tmp_17 == _tmp_16 IN
      /\ LET _tmp_18 == [_globalsScratch EXCEPT !["map"] = ((_frames[self][Len(_frames[self])].x :> _tmp_17) @@ _globalsScratch["map"])] IN
        /\ TRUE
        /\ LET _tmp_19 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
          /\ LET _tmp_20 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
            /\ _frames' = _tmp_19
            /\ _globalsScratch' = _tmp_18
            /\ _pc' = _tmp_20
            /\ UNCHANGED _actor
            /\ UNCHANGED _ret
            /\ UNCHANGED map
  /\ UNCHANGED map
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, map>>
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _main_line00005_pick(_pid)
    \/ _main_line00006_pick(_pid)
    \/ _main_line00007_pick(_pid)
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include NondeterministicAssignment.ezs

Invariant == \A x \in DOMAIN map: x > 1

=====================
