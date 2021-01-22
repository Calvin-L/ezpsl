---- MODULE Refinement ----

EXTENDS Integers, Sequences, TLC

\* #include Refinement.ezs
CONSTANTS _Undefined, increment_calls
VARIABLES _pc, _frames, _globalsScratch, _ret, _actor, x, y
vars == <<_pc, _frames, _globalsScratch, _ret, _actor, x, y>>
symmetry == UNION {Permutations(increment_calls)}
Init ==
  /\ _pc = [_pid \in increment_calls |-> <<"_begin">>]
  /\ _frames = [_pid \in increment_calls |-> << <<>> >>]
  /\ _globalsScratch = _Undefined
  /\ _ret = [_pid \in increment_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ x = (0)
  /\ y = (0)
_halt(self) ==
  /\ (_actor = self)
  /\ (_pc[self] = <<>>)
  /\ LET _tmp == _Undefined IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = <<>>] IN
        /\ LET _tmp_3 == _globalsScratch["x"] IN
          /\ LET _tmp_4 == _globalsScratch["y"] IN
            /\ LET _tmp_5 == _Undefined IN
              /\ _actor' = _tmp
              /\ _frames' = _tmp_2
              /\ _globalsScratch' = _tmp_5
              /\ _ret' = _tmp_1
              /\ x' = _tmp_3
              /\ y' = _tmp_4
              /\ UNCHANGED _pc
_begin_increment(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_6 == self IN
    /\ (self \in increment_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_7 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_increment_line00006_test_loop_condition">>)] IN
      /\ LET _tmp_8 == [x |-> x, y |-> y] IN
        /\ _actor' = _tmp_6
        /\ _globalsScratch' = _tmp_8
        /\ _pc' = _tmp_7
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
        /\ UNCHANGED y
_increment_line00006_test_loop_condition(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00006_test_loop_condition")
  /\ (_actor = self)
  /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_globalsScratch["x"] < 5) THEN "_increment_line00007_pick" ELSE "_increment_line00006_exit_loop")>>)] IN
    /\ _pc' = _tmp_9
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED x
    /\ UNCHANGED y
_increment_line00007_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00007_pick")
  /\ (_actor = self)
  /\ \E _tmp_10 \in {(_globalsScratch["x"] + 1)}:
    /\ LET _tmp_11 == _tmp_10 IN
      /\ LET _tmp_12 == [_globalsScratch EXCEPT !["x"] = _tmp_11] IN
        /\ TRUE
        /\ LET _tmp_13 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_increment_line00008_pick">>)] IN
          /\ _globalsScratch' = _tmp_12
          /\ _pc' = _tmp_13
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED x
          /\ UNCHANGED y
_increment_line00008_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00008_pick")
  /\ (_actor = self)
  /\ \E _tmp_14 \in {(_globalsScratch["y"] + 1)}:
    /\ LET _tmp_15 == _tmp_14 IN
      /\ LET _tmp_16 == [_globalsScratch EXCEPT !["y"] = _tmp_15] IN
        /\ TRUE
        /\ LET _tmp_17 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_increment_line00009_yield">>)] IN
          /\ _globalsScratch' = _tmp_16
          /\ _pc' = _tmp_17
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED x
          /\ UNCHANGED y
_increment_line00009_yield(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00009_yield")
  /\ (_actor = self)
  /\ LET _tmp_18 == _globalsScratch["x"] IN
    /\ LET _tmp_19 == _globalsScratch["y"] IN
      /\ LET _tmp_20 == _Undefined IN
        /\ LET _tmp_21 == _Undefined IN
          /\ LET _tmp_22 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_increment_line00009_yield_resume">>)] IN
            /\ _actor' = _tmp_21
            /\ _globalsScratch' = _tmp_20
            /\ _pc' = _tmp_22
            /\ x' = _tmp_18
            /\ y' = _tmp_19
            /\ UNCHANGED _frames
            /\ UNCHANGED _ret
_increment_line00009_yield_resume(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00009_yield_resume")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_23 == self IN
    /\ LET _tmp_24 == [x |-> x, y |-> y] IN
      /\ LET _tmp_25 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_increment_line00006_test_loop_condition">>)] IN
        /\ _actor' = _tmp_23
        /\ _globalsScratch' = _tmp_24
        /\ _pc' = _tmp_25
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
        /\ UNCHANGED y
_increment_line00006_exit_loop(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_increment_line00006_exit_loop")
  /\ (_actor = self)
  /\ LET _tmp_26 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_27 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_26
      /\ _pc' = _tmp_27
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED x
      /\ UNCHANGED y
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {increment_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, x, y>>
Next ==
  \E _pid \in UNION {increment_calls}:
    \/ _halt(_pid)
    \/ _begin_increment(_pid)
    \/ _increment_line00006_test_loop_condition(_pid)
    \/ _increment_line00007_pick(_pid)
    \/ _increment_line00008_pick(_pid)
    \/ _increment_line00009_yield(_pid)
    \/ _increment_line00009_yield_resume(_pid)
    \/ _increment_line00006_exit_loop(_pid)
    \/ _halt(_pid)
    \/ _begin_increment(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Refinement.ezs

Abstract == INSTANCE RefinementAbstract

Correct == Abstract!Spec
Live == WF_vars(Next) => <>[](\A p \in increment_calls: _pc[p] = <<>>)

===========================
