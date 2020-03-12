---- MODULE While ----

EXTENDS Integers, Sequences, TLC

\* #include While.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _ret, _actor, x
vars == <<_pc, _frames, _ret, _actor, x>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_main">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ x = TRUE
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ LET _tmp_1 == ~x IN
      /\ LET _tmp_2 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main">>)] IN
        /\ _actor' = _tmp
        /\ _pc' = _tmp_2
        /\ x' = _tmp_1
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_line_00009(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_3 == self IN
    /\ LET _tmp_4 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00010">>)] IN
      /\ _actor' = _tmp_3
      /\ _pc' = _tmp_4
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED x
_line_00010(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00010")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_5 == self IN
    /\ LET _tmp_6 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_7 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_8 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_5
          /\ _frames' = _tmp_7
          /\ _pc' = _tmp_8
          /\ _ret' = _tmp_6
          /\ UNCHANGED x
_main(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_9 == self IN
    /\ LET _tmp_10 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF TRUE THEN "_line_00007" ELSE "_line_00009")>>)] IN
      /\ _actor' = _tmp_9
      /\ _pc' = _tmp_10
      /\ UNCHANGED _frames
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
    \/ _line_00009(_pid)
    \/ _line_00010(_pid)
    \/ _main(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls}:
    /\ (((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_line_00009")) => FALSE)
\* /include While.ezs

=====================
