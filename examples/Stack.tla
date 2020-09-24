---- MODULE Stack ----

EXTENDS Integers, Sequences, TLC

CONSTANT Null

\* #include Stack.ezs
CONSTANTS _Undefined, dequeue_calls, enqueue_calls
VARIABLES _pc, _frames, _globalsScratch, _ret, _actor, head
vars == <<_pc, _frames, _globalsScratch, _ret, _actor, head>>
symmetry == UNION {Permutations(dequeue_calls), Permutations(enqueue_calls)}
Init ==
  /\ _pc = [_pid \in dequeue_calls |-> <<"_begin">>] @@ [_pid \in enqueue_calls |-> <<"_begin">>]
  /\ _frames = [_pid \in dequeue_calls |-> << <<>> >>] @@ [_pid \in enqueue_calls |-> << <<>> >>]
  /\ _globalsScratch = _Undefined
  /\ _ret = [_pid \in dequeue_calls |-> _Undefined] @@ [_pid \in enqueue_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ head = (Null)
_halt(self) ==
  /\ (_actor = self)
  /\ (_pc[self] = <<>>)
  /\ LET _tmp == _Undefined IN
    /\ LET _tmp_1 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_2 == [_frames EXCEPT ![self] = <<>>] IN
        /\ LET _tmp_3 == _globalsScratch["head"] IN
          /\ LET _tmp_4 == _Undefined IN
            /\ _actor' = _tmp
            /\ _frames' = _tmp_2
            /\ _globalsScratch' = _tmp_4
            /\ _ret' = _tmp_1
            /\ head' = _tmp_3
            /\ UNCHANGED _pc
_begin_dequeue(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_5 == self IN
    /\ (self \in dequeue_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00015_pick">>)] IN
      /\ LET _tmp_7 == [head |-> head] IN
        /\ _actor' = _tmp_5
        /\ _globalsScratch' = _tmp_7
        /\ _pc' = _tmp_6
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_begin_enqueue(self) ==
  /\ (_actor = _Undefined)
  /\ LET _tmp_8 == self IN
    /\ (self \in enqueue_calls)
    /\ (Len(_pc[self]) > 0)
    /\ (_pc[self][Len(_pc[self])] = "_begin")
    /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00005_pick">>)] IN
      /\ LET _tmp_10 == [head |-> head] IN
        /\ _actor' = _tmp_8
        /\ _globalsScratch' = _tmp_10
        /\ _pc' = _tmp_9
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_enqueue_line00005_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00005_pick")
  /\ (_actor = self)
  /\ \E _tmp_11 \in {Null}:
    /\ LET _tmp_12 == _tmp_11 IN
      /\ LET _tmp_13 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_12) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_14 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00006_pick">>)] IN
          /\ _frames' = _tmp_13
          /\ _pc' = _tmp_14
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_enqueue_line00006_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00006_pick")
  /\ (_actor = self)
  /\ \E _tmp_15 \in {FALSE}:
    /\ LET _tmp_16 == _tmp_15 IN
      /\ LET _tmp_17 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _tmp_16) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_18 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00007_test_loop_condition">>)] IN
          /\ _frames' = _tmp_17
          /\ _pc' = _tmp_18
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_enqueue_line00007_test_loop_condition(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00007_test_loop_condition")
  /\ (_actor = self)
  /\ LET _tmp_19 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_enqueue_line00008_call_read" ELSE "_enqueue_line00007_exit_loop")>>)] IN
    /\ _pc' = _tmp_19
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_enqueue_line00008_call_read(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00008_call_read")
  /\ (_actor = self)
  /\ LET _tmp_20 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
    /\ LET _tmp_21 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00008_return_from_read">>) \o <<"_read_line00026_pick">>)] IN
      /\ _frames' = _tmp_20
      /\ _pc' = _tmp_21
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_enqueue_line00008_return_from_read(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00008_return_from_read")
  /\ (_actor = self)
  /\ LET _tmp_22 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_23 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00009_call_CAS">>)] IN
      /\ _frames' = _tmp_22
      /\ _pc' = _tmp_23
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_enqueue_line00009_call_CAS(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00009_call_CAS")
  /\ (_actor = self)
  /\ LET _tmp_24 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> [value |-> self, next |-> _frames[self][Len(_frames[self])].tmp]]>>)] IN
    /\ LET _tmp_25 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00009_return_from_CAS">>) \o <<"_CAS_line00032_if_branch">>)] IN
      /\ _frames' = _tmp_24
      /\ _pc' = _tmp_25
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_enqueue_line00009_return_from_CAS(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00009_return_from_CAS")
  /\ (_actor = self)
  /\ LET _tmp_26 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_27 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_enqueue_line00007_test_loop_condition">>)] IN
      /\ _frames' = _tmp_26
      /\ _pc' = _tmp_27
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_enqueue_line00007_exit_loop(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue_line00007_exit_loop")
  /\ (_actor = self)
  /\ LET _tmp_28 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_29 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_28
      /\ _pc' = _tmp_29
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue_line00015_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00015_pick")
  /\ (_actor = self)
  /\ \E _tmp_30 \in {Null}:
    /\ LET _tmp_31 == _tmp_30 IN
      /\ LET _tmp_32 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_31) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_33 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00016_pick">>)] IN
          /\ _frames' = _tmp_32
          /\ _pc' = _tmp_33
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_dequeue_line00016_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00016_pick")
  /\ (_actor = self)
  /\ \E _tmp_34 \in {FALSE}:
    /\ LET _tmp_35 == _tmp_34 IN
      /\ LET _tmp_36 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _tmp_35) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_37 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00017_test_loop_condition">>)] IN
          /\ _frames' = _tmp_36
          /\ _pc' = _tmp_37
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_dequeue_line00017_test_loop_condition(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00017_test_loop_condition")
  /\ (_actor = self)
  /\ LET _tmp_38 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_dequeue_line00018_call_read" ELSE "_dequeue_line00017_exit_loop")>>)] IN
    /\ _pc' = _tmp_38
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_dequeue_line00018_call_read(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00018_call_read")
  /\ (_actor = self)
  /\ LET _tmp_39 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
    /\ LET _tmp_40 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00018_return_from_read">>) \o <<"_read_line00026_pick">>)] IN
      /\ _frames' = _tmp_39
      /\ _pc' = _tmp_40
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue_line00018_return_from_read(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00018_return_from_read")
  /\ (_actor = self)
  /\ LET _tmp_41 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_42 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00019_if_branch">>)] IN
      /\ _frames' = _tmp_41
      /\ _pc' = _tmp_42
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue_line00019_if_branch(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00019_if_branch")
  /\ (_actor = self)
  /\ LET _tmp_43 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_frames[self][Len(_frames[self])].tmp /= Null) THEN "_dequeue_line00020_call_CAS" ELSE "_dequeue_line00022_skip")>>)] IN
    /\ _pc' = _tmp_43
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_dequeue_line00020_call_CAS(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00020_call_CAS")
  /\ (_actor = self)
  /\ LET _tmp_44 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> _frames[self][Len(_frames[self])].tmp.next]>>)] IN
    /\ LET _tmp_45 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00020_return_from_CAS">>) \o <<"_CAS_line00032_if_branch">>)] IN
      /\ _frames' = _tmp_44
      /\ _pc' = _tmp_45
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue_line00020_return_from_CAS(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00020_return_from_CAS")
  /\ (_actor = self)
  /\ LET _tmp_46 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_47 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00017_test_loop_condition">>)] IN
      /\ _frames' = _tmp_46
      /\ _pc' = _tmp_47
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue_line00022_skip(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00022_skip")
  /\ (_actor = self)
  /\ LET _tmp_48 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_dequeue_line00017_test_loop_condition">>)] IN
    /\ _pc' = _tmp_48
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_dequeue_line00017_exit_loop(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue_line00017_exit_loop")
  /\ (_actor = self)
  /\ LET _tmp_49 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_50 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_49
      /\ _pc' = _tmp_50
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_read_line00026_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_read_line00026_pick")
  /\ (_actor = self)
  /\ \E _tmp_51 \in {_globalsScratch["head"]}:
    /\ LET _tmp_52 == _tmp_51 IN
      /\ LET _tmp_53 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_52) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_54 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_read_line00027_yield">>)] IN
          /\ _frames' = _tmp_53
          /\ _pc' = _tmp_54
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_read_line00027_yield(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_read_line00027_yield")
  /\ (_actor = self)
  /\ LET _tmp_55 == _globalsScratch["head"] IN
    /\ LET _tmp_56 == _Undefined IN
      /\ LET _tmp_57 == _Undefined IN
        /\ LET _tmp_58 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_read_line00027_yield_resume">>)] IN
          /\ _actor' = _tmp_57
          /\ _globalsScratch' = _tmp_56
          /\ _pc' = _tmp_58
          /\ head' = _tmp_55
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_read_line00027_yield_resume(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_read_line00027_yield_resume")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_59 == self IN
    /\ LET _tmp_60 == [head |-> head] IN
      /\ LET _tmp_61 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_read_line00028_return">>)] IN
        /\ _actor' = _tmp_59
        /\ _globalsScratch' = _tmp_60
        /\ _pc' = _tmp_61
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_read_line00028_return(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_read_line00028_return")
  /\ (_actor = self)
  /\ LET _tmp_62 == [_ret EXCEPT ![self] = _frames[self][Len(_frames[self])].tmp] IN
    /\ LET _tmp_63 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
      /\ LET _tmp_64 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
        /\ _frames' = _tmp_63
        /\ _pc' = _tmp_64
        /\ _ret' = _tmp_62
        /\ UNCHANGED _actor
        /\ UNCHANGED _globalsScratch
        /\ UNCHANGED head
_CAS_line00032_if_branch(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00032_if_branch")
  /\ (_actor = self)
  /\ LET _tmp_65 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_globalsScratch["head"] = _frames[self][Len(_frames[self])].expected) THEN "_CAS_line00033_pick" ELSE "_CAS_line00037_skip")>>)] IN
    /\ _pc' = _tmp_65
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_CAS_line00033_pick(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00033_pick")
  /\ (_actor = self)
  /\ \E _tmp_66 \in {_frames[self][Len(_frames[self])].new}:
    /\ LET _tmp_67 == _tmp_66 IN
      /\ LET _tmp_68 == [_globalsScratch EXCEPT !["head"] = _tmp_67] IN
        /\ TRUE
        /\ LET _tmp_69 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00034_yield">>)] IN
          /\ _globalsScratch' = _tmp_68
          /\ _pc' = _tmp_69
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_CAS_line00034_yield(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00034_yield")
  /\ (_actor = self)
  /\ LET _tmp_70 == _globalsScratch["head"] IN
    /\ LET _tmp_71 == _Undefined IN
      /\ LET _tmp_72 == _Undefined IN
        /\ LET _tmp_73 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00034_yield_resume">>)] IN
          /\ _actor' = _tmp_72
          /\ _globalsScratch' = _tmp_71
          /\ _pc' = _tmp_73
          /\ head' = _tmp_70
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_CAS_line00034_yield_resume(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00034_yield_resume")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_74 == self IN
    /\ LET _tmp_75 == [head |-> head] IN
      /\ LET _tmp_76 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00035_return">>)] IN
        /\ _actor' = _tmp_74
        /\ _globalsScratch' = _tmp_75
        /\ _pc' = _tmp_76
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_CAS_line00035_return(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00035_return")
  /\ (_actor = self)
  /\ LET _tmp_77 == [_ret EXCEPT ![self] = TRUE] IN
    /\ LET _tmp_78 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
      /\ LET _tmp_79 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
        /\ _frames' = _tmp_78
        /\ _pc' = _tmp_79
        /\ _ret' = _tmp_77
        /\ UNCHANGED _actor
        /\ UNCHANGED _globalsScratch
        /\ UNCHANGED head
_CAS_line00037_skip(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00037_skip")
  /\ (_actor = self)
  /\ LET _tmp_80 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00037_yield">>)] IN
    /\ _pc' = _tmp_80
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_CAS_line00037_yield(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00037_yield")
  /\ (_actor = self)
  /\ LET _tmp_81 == _globalsScratch["head"] IN
    /\ LET _tmp_82 == _Undefined IN
      /\ LET _tmp_83 == _Undefined IN
        /\ LET _tmp_84 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00037_yield_resume">>)] IN
          /\ _actor' = _tmp_83
          /\ _globalsScratch' = _tmp_82
          /\ _pc' = _tmp_84
          /\ head' = _tmp_81
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_CAS_line00037_yield_resume(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00037_yield_resume")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_85 == self IN
    /\ LET _tmp_86 == [head |-> head] IN
      /\ LET _tmp_87 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_CAS_line00038_return">>)] IN
        /\ _actor' = _tmp_85
        /\ _globalsScratch' = _tmp_86
        /\ _pc' = _tmp_87
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_CAS_line00038_return(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS_line00038_return")
  /\ (_actor = self)
  /\ LET _tmp_88 == [_ret EXCEPT ![self] = FALSE] IN
    /\ LET _tmp_89 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
      /\ LET _tmp_90 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
        /\ _frames' = _tmp_89
        /\ _pc' = _tmp_90
        /\ _ret' = _tmp_88
        /\ UNCHANGED _actor
        /\ UNCHANGED _globalsScratch
        /\ UNCHANGED head
  /\ UNCHANGED head
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {dequeue_calls, enqueue_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _globalsScratch, _ret, _actor, head>>
Next ==
  \E _pid \in UNION {dequeue_calls, enqueue_calls}:
    \/ _halt(_pid)
    \/ _begin_dequeue(_pid)
    \/ _begin_enqueue(_pid)
    \/ _enqueue_line00005_pick(_pid)
    \/ _enqueue_line00006_pick(_pid)
    \/ _enqueue_line00007_test_loop_condition(_pid)
    \/ _enqueue_line00008_call_read(_pid)
    \/ _enqueue_line00008_return_from_read(_pid)
    \/ _enqueue_line00009_call_CAS(_pid)
    \/ _enqueue_line00009_return_from_CAS(_pid)
    \/ _enqueue_line00007_exit_loop(_pid)
    \/ _dequeue_line00015_pick(_pid)
    \/ _dequeue_line00016_pick(_pid)
    \/ _dequeue_line00017_test_loop_condition(_pid)
    \/ _dequeue_line00018_call_read(_pid)
    \/ _dequeue_line00018_return_from_read(_pid)
    \/ _dequeue_line00019_if_branch(_pid)
    \/ _dequeue_line00020_call_CAS(_pid)
    \/ _dequeue_line00020_return_from_CAS(_pid)
    \/ _dequeue_line00022_skip(_pid)
    \/ _dequeue_line00017_exit_loop(_pid)
    \/ _read_line00026_pick(_pid)
    \/ _read_line00027_yield(_pid)
    \/ _read_line00027_yield_resume(_pid)
    \/ _read_line00028_return(_pid)
    \/ _CAS_line00032_if_branch(_pid)
    \/ _CAS_line00033_pick(_pid)
    \/ _CAS_line00034_yield(_pid)
    \/ _CAS_line00034_yield_resume(_pid)
    \/ _CAS_line00035_return(_pid)
    \/ _CAS_line00037_skip(_pid)
    \/ _CAS_line00037_yield(_pid)
    \/ _CAS_line00037_yield_resume(_pid)
    \/ _CAS_line00038_return(_pid)
    \/ _halt(_pid)
    \/ _begin_dequeue(_pid)
    \/ _begin_enqueue(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Stack.ezs

=====================
