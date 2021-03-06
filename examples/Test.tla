---- MODULE Test ----

EXTENDS Integers, Sequences, TLC

\* #include Test.ezs
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
  /\ x = (0)
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
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00005_pick">>)] IN
      /\ LET _tmp_7 == [x |-> x] IN
        /\ _actor' = _tmp_5
        /\ _globalsScratch' = _tmp_7
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
_main_line00005_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00005_pick")
  /\ (_actor = self)
  /\ \E _tmp_8 \in {_globalsScratch["x"]}:
    /\ LET _tmp_9 == _tmp_8 IN
      /\ LET _tmp_10 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_9) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_11 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00006_yield">>)] IN
          /\ _frames' = _tmp_10
          /\ _pc' = _tmp_11
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED x
_main_line00006_yield(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00006_yield")
  /\ (_actor = self)
  /\ LET _tmp_12 == _globalsScratch["x"] IN
    /\ LET _tmp_13 == _Undefined IN
      /\ LET _tmp_14 == _Undefined IN
        /\ LET _tmp_15 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00006_yield_resume">>)] IN
          /\ _actor' = _tmp_14
          /\ _globalsScratch' = _tmp_13
          /\ _pc' = _tmp_15
          /\ x' = _tmp_12
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_main_line00006_yield_resume(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00006_yield_resume")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_16 == self IN
    /\ LET _tmp_17 == [x |-> x] IN
      /\ LET _tmp_18 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_main_line00007_pick">>)] IN
        /\ _actor' = _tmp_16
        /\ _globalsScratch' = _tmp_17
        /\ _pc' = _tmp_18
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED x
_main_line00007_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_main_line00007_pick")
  /\ (_actor = self)
  /\ \E _tmp_19 \in {(_frames[self][Len(_frames[self])].tmp + 1)}:
    /\ LET _tmp_20 == _tmp_19 IN
      /\ LET _tmp_21 == [_globalsScratch EXCEPT !["x"] = _tmp_20] IN
        /\ TRUE
        /\ LET _tmp_22 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
          /\ LET _tmp_23 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
            /\ _frames' = _tmp_22
            /\ _globalsScratch' = _tmp_21
            /\ _pc' = _tmp_23
            /\ UNCHANGED _actor
            /\ UNCHANGED _ret
            /\ UNCHANGED x
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {main_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, x>>
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _main_line00005_pick(_pid)
    \/ _main_line00006_yield(_pid)
    \/ _main_line00006_yield_resume(_pid)
    \/ _main_line00007_pick(_pid)
    \/ _halt(_pid)
    \/ _begin_main(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Test.ezs

Invariant ==
  /\ x <= 2
  /\ (\A c \in main_calls: _pc[c] = <<>>) => (x = 2)

=====================
