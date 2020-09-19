---- MODULE While ----

EXTENDS Integers, Sequences, TLC

\* #include While.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _ret, _actor, x
vars == <<_pc, _frames, _ret, _actor, x>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_line_00005">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ x = TRUE
_line_00005(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00005")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ LET _tmp_1 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF TRUE THEN "_line_00006" ELSE "_line_00005_1")>>)] IN
      /\ _actor' = _tmp
      /\ _pc' = _tmp_1
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED x
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_2 == self IN
    /\ \E _tmp_3 \in {~x}:
      /\ LET _tmp_4 == _tmp_3 IN
        /\ LET _tmp_5 == _tmp_4 IN
          /\ TRUE
          /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00005">>)] IN
            /\ _actor' = _tmp_2
            /\ _pc' = _tmp_6
            /\ x' = _tmp_5
            /\ UNCHANGED _frames
            /\ UNCHANGED _ret
_line_00005_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00005_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_7 == self IN
    /\ LET _tmp_8 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00008">>)] IN
      /\ _actor' = _tmp_7
      /\ _pc' = _tmp_8
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED x
_line_00008(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00008")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_9 == self IN
    /\ LET _tmp_10 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
      /\ LET _tmp_11 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
        /\ _actor' = _tmp_9
        /\ _frames' = _tmp_10
        /\ _pc' = _tmp_11
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
    \/ _line_00005(_pid)
    \/ _line_00006(_pid)
    \/ _line_00005_1(_pid)
    \/ _line_00008(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls}:
    /\ (_actor \in {_Undefined, self}) => ((((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_line_00008")) => FALSE))
\* /include While.ezs

=====================
