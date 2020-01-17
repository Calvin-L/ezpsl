---- MODULE Test ----

EXTENDS Integers, Sequences, TLC

\* #include Test.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _ret, _actor, x
vars == <<_pc, _frames, _ret, _actor, x>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_main">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ x = 0
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ LET _tmp_1 == _Undefined IN
      /\ LET _tmp_2 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00008">>)] IN
        /\ _actor' = _tmp_1
        /\ _pc' = _tmp_2
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
_line_00008(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00008")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_3 == self IN
    /\ LET _tmp_4 == (_frames[self][Len(_frames[self])].tmp + 1) IN
      /\ LET _tmp_5 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00009">>)] IN
        /\ _actor' = _tmp_3
        /\ _pc' = _tmp_5
        /\ x' = _tmp_4
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_line_00009(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_6 == self IN
    /\ LET _tmp_7 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_8 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_9 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_6
          /\ _frames' = _tmp_8
          /\ _pc' = _tmp_9
          /\ _ret' = _tmp_7
          /\ UNCHANGED x
_main(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_10 == self IN
    /\ LET _tmp_11 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> x) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_12 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
        /\ _actor' = _tmp_10
        /\ _frames' = _tmp_11
        /\ _pc' = _tmp_12
        /\ UNCHANGED _ret
        /\ UNCHANGED x
_halt(self) ==
  /\ _pc[self] = <<>>
  /\ _actor = self
  /\ _actor' = _Undefined
  /\ _ret' = [_ret EXCEPT ![self] = _Undefined]
  /\ UNCHANGED _frames
  /\ UNCHANGED _pc
  /\ UNCHANGED x
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _ret, _actor, x>>
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _line_00007(_pid)
    \/ _line_00008(_pid)
    \/ _line_00009(_pid)
    \/ _main(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Test.ezs

Invariant ==
  /\ (_actor = _Undefined) => (x <= 2)
  /\ (\A c \in main_calls: _pc[c] = <<>>) => (x = 2)

=====================
