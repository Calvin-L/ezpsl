---- MODULE NondeterministicAssignment ----

EXTENDS Integers, Sequences, TLC, FiniteSets

\* #include NondeterministicAssignment.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _ret, _actor, map
vars == <<_pc, _frames, _ret, _actor, map>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_main">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ map = <<>>
_line_00004(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00004")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_3 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp
          /\ _frames' = _tmp_2
          /\ _pc' = _tmp_3
          /\ _ret' = _tmp_1
          /\ UNCHANGED map
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_4 == self IN
    /\ \E _tmp_5 \in {1, 2, 3}:
      /\ LET _tmp_6 == _tmp_5 IN
        /\ LET _tmp_7 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("x" :> _tmp_6) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
          /\ (_tmp_7[self][Len(_tmp_7[self])].x > 1)
          /\ LET _tmp_8 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
            /\ _actor' = _tmp_4
            /\ _frames' = _tmp_7
            /\ _pc' = _tmp_8
            /\ UNCHANGED _ret
            /\ UNCHANGED map
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_9 == self IN
    /\ LET _tmp_10 == ((_frames[self][Len(_frames[self])].x :> TRUE) @@ map) IN
      /\ LET _tmp_11 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00004">>)] IN
        /\ _actor' = _tmp_9
        /\ _pc' = _tmp_11
        /\ map' = _tmp_10
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_main(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_12 == self IN
    /\ LET _tmp_13 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("x" :> 0) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_14 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006">>)] IN
        /\ _actor' = _tmp_12
        /\ _frames' = _tmp_13
        /\ _pc' = _tmp_14
        /\ UNCHANGED _ret
        /\ UNCHANGED map
_halt(self) ==
  /\ _pc[self] = <<>>
  /\ _actor = self
  /\ _actor' = _Undefined
  /\ _ret' = [_ret EXCEPT ![self] = _Undefined]
  /\ UNCHANGED _frames
  /\ UNCHANGED _pc
  /\ UNCHANGED map
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _ret, _actor, map>>
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _line_00004(_pid)
    \/ _line_00006(_pid)
    \/ _line_00007(_pid)
    \/ _main(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include NondeterministicAssignment.ezs

Invariant == \A x \in DOMAIN map: x > 1

=====================
