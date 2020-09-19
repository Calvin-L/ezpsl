---- MODULE Assertions ----

EXTENDS Integers, Sequences, TLC

\* #include Assertions.ezs
CONSTANTS _Undefined, main_calls, test_calls
VARIABLES _pc, _frames, _ret, _actor, ok
vars == <<_pc, _frames, _ret, _actor, ok>>
symmetry == UNION {Permutations(main_calls), Permutations(test_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_line_00005">>] @@ [_pid \in test_calls |-> <<"_line_00012">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>] @@ [_pid \in test_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined] @@ [_pid \in test_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ ok = TRUE
_line_00005(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00005")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ \E _tmp_1 \in {FALSE}:
      /\ LET _tmp_2 == _tmp_1 IN
        /\ LET _tmp_3 == _tmp_2 IN
          /\ TRUE
          /\ LET _tmp_4 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006">>)] IN
            /\ _actor' = _tmp
            /\ _pc' = _tmp_4
            /\ ok' = _tmp_3
            /\ UNCHANGED _frames
            /\ UNCHANGED _ret
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_5 == self IN
    /\ LET _tmp_6 == _Undefined IN
      /\ LET _tmp_7 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006_1">>)] IN
        /\ _actor' = _tmp_6
        /\ _pc' = _tmp_7
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_line_00006_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_8 == self IN
    /\ TRUE
    /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
      /\ _actor' = _tmp_8
      /\ _pc' = _tmp_9
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED ok
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_10 == self IN
    /\ \E _tmp_11 \in {TRUE}:
      /\ LET _tmp_12 == _tmp_11 IN
        /\ LET _tmp_13 == _tmp_12 IN
          /\ TRUE
          /\ LET _tmp_14 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
            /\ LET _tmp_15 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
              /\ _actor' = _tmp_10
              /\ _frames' = _tmp_14
              /\ _pc' = _tmp_15
              /\ ok' = _tmp_13
              /\ UNCHANGED _ret
_line_00012(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00012")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_16 == self IN
    /\ LET _tmp_17 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
      /\ LET _tmp_18 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
        /\ _actor' = _tmp_16
        /\ _frames' = _tmp_17
        /\ _pc' = _tmp_18
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_halt(self) ==
  /\ _pc[self] = <<>>
  /\ _actor = self
  /\ _actor' = _Undefined
  /\ _ret' = [_ret EXCEPT ![self] = _Undefined]
  /\ UNCHANGED _frames
  /\ UNCHANGED _pc
  /\ UNCHANGED ok
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls, test_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _ret, _actor, ok>>
Next ==
  \E _pid \in UNION {main_calls, test_calls}:
    \/ _line_00005(_pid)
    \/ _line_00006(_pid)
    \/ _line_00006_1(_pid)
    \/ _line_00007(_pid)
    \/ _line_00012(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls, test_calls}:
    /\ (_actor \in {_Undefined, self}) => ((((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_line_00012")) => ok))
\* /include Assertions.ezs

=====================
