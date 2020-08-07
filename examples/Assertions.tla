---- MODULE Assertions ----

EXTENDS Integers, Sequences, TLC

\* #include Assertions.ezs
CONSTANTS _Undefined, main_calls, test_calls
VARIABLES _pc, _frames, _ret, _actor, ok
vars == <<_pc, _frames, _ret, _actor, ok>>
symmetry == UNION {Permutations(main_calls), Permutations(test_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_main">>] @@ [_pid \in test_calls |-> <<"_test">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>] @@ [_pid \in test_calls |-> << <<>> >>]
  /\ _ret = [_pid \in main_calls |-> _Undefined] @@ [_pid \in test_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ ok = TRUE
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
          /\ UNCHANGED ok
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_4 == self IN
    /\ LET _tmp_5 == _Undefined IN
      /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
        /\ _actor' = _tmp_5
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_7 == self IN
    /\ LET _tmp_8 == TRUE IN
      /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00004">>)] IN
        /\ _actor' = _tmp_7
        /\ _pc' = _tmp_9
        /\ ok' = _tmp_8
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_line_00011(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00011")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_10 == self IN
    /\ LET _tmp_11 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_12 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_13 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_10
          /\ _frames' = _tmp_12
          /\ _pc' = _tmp_13
          /\ _ret' = _tmp_11
          /\ UNCHANGED ok
_main(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_14 == self IN
    /\ LET _tmp_15 == FALSE IN
      /\ LET _tmp_16 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006">>)] IN
        /\ _actor' = _tmp_14
        /\ _pc' = _tmp_16
        /\ ok' = _tmp_15
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_test(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_test")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_17 == self IN
    /\ LET _tmp_18 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00011">>)] IN
      /\ _actor' = _tmp_17
      /\ _pc' = _tmp_18
      /\ UNCHANGED _frames
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
    \/ _line_00004(_pid)
    \/ _line_00006(_pid)
    \/ _line_00007(_pid)
    \/ _line_00011(_pid)
    \/ _main(_pid)
    \/ _test(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls, test_calls}:
    /\ (_actor \in {_Undefined, self}) => ((((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_test")) => ok))
\* /include Assertions.ezs

=====================
