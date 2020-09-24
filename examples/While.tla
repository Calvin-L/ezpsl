---- MODULE While ----

EXTENDS Integers, Sequences, TLC

\* #include While.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _globalsScratch, _ret, _actor, x
vars == <<_pc, _frames, _globalsScratch, _ret, _actor, x>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_begin">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _globalsScratch = _Undefined
  /\ _ret = [_pid \in main_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ x = (TRUE)
_halt(self) ==
  /\ (_actor = self)
  /\ (_pc[self] = <<>>)
  /\ LET _tmp == _Undefined IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = <<>>] IN
        /\ LET _tmp_3 == _globalsScratch["x"] IN
          /\ LET _tmp_4 == _Undefined IN
            /\ _actor' = _tmp
            /\ _frames' = _tmp_2
            /\ _globalsScratch' = _tmp_4
            /\ _ret' = _tmp_1
            /\ x' = _tmp_3
            /\ UNCHANGED _pc
_begin_main(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_5 == self IN
    /\ (self \in main_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00005_test_loop_condition">>)] IN
      /\ LET _tmp_7 == [x |-> x] IN
        /\ _actor' = _tmp_5
        /\ _globalsScratch' = _tmp_7
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
_main_line00005_test_loop_condition(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00005_test_loop_condition")
  /\ (_actor = self)
  /\ LET _tmp_8 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF TRUE THEN "_main_line00006_pick" ELSE "_main_line00005_exit_loop")>>)] IN
    /\ _pc' = _tmp_8
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED x
_main_line00006_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00006_pick")
  /\ (_actor = self)
  /\ \E _tmp_9 \in {~_globalsScratch["x"]}:
    /\ LET _tmp_10 == _tmp_9 IN
      /\ LET _tmp_11 == [_globalsScratch EXCEPT !["x"] = _tmp_10] IN
        /\ TRUE
        /\ LET _tmp_12 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00005_test_loop_condition">>)] IN
          /\ _globalsScratch' = _tmp_11
          /\ _pc' = _tmp_12
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED x
_main_line00005_exit_loop(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00005_exit_loop")
  /\ (_actor = self)
  /\ LET _tmp_13 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00008_assert">>)] IN
    /\ _pc' = _tmp_13
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED x
_main_line00008_assert(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00008_assert")
  /\ (_actor = self)
  /\ LET _tmp_14 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_15 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_14
      /\ _pc' = _tmp_15
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED x
  /\ UNCHANGED x
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, x>>
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _main_line00005_test_loop_condition(_pid)
    \/ _main_line00006_pick(_pid)
    \/ _main_line00005_exit_loop(_pid)
    \/ _main_line00008_assert(_pid)
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls}:
    /\ (_actor = self) => ((((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_main_line00008_assert")) => FALSE))
\* /include While.ezs

=====================
