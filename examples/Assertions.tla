---- MODULE Assertions ----

EXTENDS Integers, Sequences, TLC

\* #include Assertions.ezs
CONSTANTS _Undefined, main_calls, test_calls
VARIABLES _pc, _frames, _globalsScratch, _ret, _actor, ok
vars == <<_pc, _frames, _globalsScratch, _ret, _actor, ok>>
symmetry == UNION {Permutations(main_calls), Permutations(test_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_begin">>] @@ [_pid \in test_calls |-> <<"_begin">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>] @@ [_pid \in test_calls |-> << <<>> >>]
  /\ _globalsScratch = _Undefined
  /\ _ret = [_pid \in main_calls |-> _Undefined] @@ [_pid \in test_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ ok = TRUE
_halt(self) ==
  /\ (_actor = self)
  /\ (_pc[self] = <<>>)
  /\ LET _tmp == _Undefined IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = <<>>] IN
        /\ LET _tmp_3 == _globalsScratch["ok"] IN
          /\ LET _tmp_4 == _Undefined IN
            /\ _actor' = _tmp
            /\ _frames' = _tmp_2
            /\ _globalsScratch' = _tmp_4
            /\ _ret' = _tmp_1
            /\ ok' = _tmp_3
            /\ UNCHANGED _pc
_begin_main(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_5 == self IN
    /\ (self \in main_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00005">>)] IN
      /\ LET _tmp_7 == [ok |-> ok] IN
        /\ _actor' = _tmp_5
        /\ _globalsScratch' = _tmp_7
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_begin_test(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_8 == self IN
    /\ (self \in test_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00012">>)] IN
      /\ LET _tmp_10 == [ok |-> ok] IN
        /\ _actor' = _tmp_8
        /\ _globalsScratch' = _tmp_10
        /\ _pc' = _tmp_9
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_line_00005(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00005")
  /\ (_actor = self)
  /\ \E _tmp_11 \in {FALSE}:
    /\ LET _tmp_12 == _tmp_11 IN
      /\ LET _tmp_13 == [_globalsScratch EXCEPT !["ok"] = _tmp_12] IN
        /\ TRUE
        /\ LET _tmp_14 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006">>)] IN
          /\ _globalsScratch' = _tmp_13
          /\ _pc' = _tmp_14
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED ok
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ (_actor = self)
  /\ LET _tmp_15 == _globalsScratch["ok"] IN
    /\ LET _tmp_16 == _Undefined IN
      /\ LET _tmp_17 == _Undefined IN
        /\ LET _tmp_18 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006_1">>)] IN
          /\ _actor' = _tmp_17
          /\ _globalsScratch' = _tmp_16
          /\ _pc' = _tmp_18
          /\ ok' = _tmp_15
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_line_00006_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006_1")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_19 == self IN
    /\ LET _tmp_20 == [ok |-> ok] IN
      /\ LET _tmp_21 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
        /\ _actor' = _tmp_19
        /\ _globalsScratch' = _tmp_20
        /\ _pc' = _tmp_21
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED ok
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ (_actor = self)
  /\ \E _tmp_22 \in {TRUE}:
    /\ LET _tmp_23 == _tmp_22 IN
      /\ LET _tmp_24 == [_globalsScratch EXCEPT !["ok"] = _tmp_23] IN
        /\ TRUE
        /\ LET _tmp_25 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
          /\ LET _tmp_26 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
            /\ _frames' = _tmp_25
            /\ _globalsScratch' = _tmp_24
            /\ _pc' = _tmp_26
            /\ UNCHANGED _actor
            /\ UNCHANGED _ret
            /\ UNCHANGED ok
_line_00012(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00012")
  /\ (_actor = self)
  /\ LET _tmp_27 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_28 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_27
      /\ _pc' = _tmp_28
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED ok
  /\ UNCHANGED ok
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls, test_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, ok>>
Next ==
  \E _pid \in UNION {main_calls, test_calls}:
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _begin_test(_pid)
    \/ _line_00005(_pid)
    \/ _line_00006(_pid)
    \/ _line_00006_1(_pid)
    \/ _line_00007(_pid)
    \/ _line_00012(_pid)
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _begin_test(_pid)
    \/ _finished
NoAssertionFailures == \A self \in UNION {main_calls, test_calls}:
    /\ (_actor = self) => ((((_pc[self] /= <<>>) /\ (_pc[self][Len(_pc[self])] = "_line_00012")) => _globalsScratch["ok"]))
\* /include Assertions.ezs

=====================
