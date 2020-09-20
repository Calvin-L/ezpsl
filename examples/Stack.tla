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
  /\ head = Null
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
    /\ LET _tmp_6 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00015">>)] IN
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
    /\ LET _tmp_9 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00005">>)] IN
      /\ LET _tmp_10 == [head |-> head] IN
        /\ _actor' = _tmp_8
        /\ _globalsScratch' = _tmp_10
        /\ _pc' = _tmp_9
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00005(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00005")
  /\ (_actor = self)
  /\ \E _tmp_11 \in {Null}:
    /\ LET _tmp_12 == _tmp_11 IN
      /\ LET _tmp_13 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_12) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_14 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00006">>)] IN
          /\ _frames' = _tmp_13
          /\ _pc' = _tmp_14
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00006(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00006")
  /\ (_actor = self)
  /\ \E _tmp_15 \in {FALSE}:
    /\ LET _tmp_16 == _tmp_15 IN
      /\ LET _tmp_17 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _tmp_16) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_18 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
          /\ _frames' = _tmp_17
          /\ _pc' = _tmp_18
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ (_actor = self)
  /\ LET _tmp_19 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_line_00008" ELSE "_line_00007_1")>>)] IN
    /\ _pc' = _tmp_19
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00008(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00008")
  /\ (_actor = self)
  /\ LET _tmp_20 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
    /\ LET _tmp_21 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00008_1">>) \o <<"_line_00026">>)] IN
      /\ _frames' = _tmp_20
      /\ _pc' = _tmp_21
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00008_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00008_1")
  /\ (_actor = self)
  /\ LET _tmp_22 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_23 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00009">>)] IN
      /\ _frames' = _tmp_22
      /\ _pc' = _tmp_23
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00009(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009")
  /\ (_actor = self)
  /\ LET _tmp_24 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> [value |-> self, next |-> _frames[self][Len(_frames[self])].tmp]]>>)] IN
    /\ LET _tmp_25 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00009_1">>) \o <<"_line_00032">>)] IN
      /\ _frames' = _tmp_24
      /\ _pc' = _tmp_25
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00009_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009_1")
  /\ (_actor = self)
  /\ LET _tmp_26 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_27 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
      /\ _frames' = _tmp_26
      /\ _pc' = _tmp_27
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00007_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007_1")
  /\ (_actor = self)
  /\ LET _tmp_28 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_29 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_28
      /\ _pc' = _tmp_29
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00015(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00015")
  /\ (_actor = self)
  /\ \E _tmp_30 \in {Null}:
    /\ LET _tmp_31 == _tmp_30 IN
      /\ LET _tmp_32 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_31) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_33 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00016">>)] IN
          /\ _frames' = _tmp_32
          /\ _pc' = _tmp_33
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00016(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00016")
  /\ (_actor = self)
  /\ \E _tmp_34 \in {FALSE}:
    /\ LET _tmp_35 == _tmp_34 IN
      /\ LET _tmp_36 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _tmp_35) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_37 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00017">>)] IN
          /\ _frames' = _tmp_36
          /\ _pc' = _tmp_37
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00017(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00017")
  /\ (_actor = self)
  /\ LET _tmp_38 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_line_00018" ELSE "_line_00017_1")>>)] IN
    /\ _pc' = _tmp_38
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00018(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00018")
  /\ (_actor = self)
  /\ LET _tmp_39 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
    /\ LET _tmp_40 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00018_1">>) \o <<"_line_00026">>)] IN
      /\ _frames' = _tmp_39
      /\ _pc' = _tmp_40
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00018_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00018_1")
  /\ (_actor = self)
  /\ LET _tmp_41 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_42 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00019">>)] IN
      /\ _frames' = _tmp_41
      /\ _pc' = _tmp_42
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00019(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00019")
  /\ (_actor = self)
  /\ LET _tmp_43 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_frames[self][Len(_frames[self])].tmp /= Null) THEN "_line_00020" ELSE "_line_00022")>>)] IN
    /\ _pc' = _tmp_43
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00020(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00020")
  /\ (_actor = self)
  /\ LET _tmp_44 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> _frames[self][Len(_frames[self])].tmp.next]>>)] IN
    /\ LET _tmp_45 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00020_1">>) \o <<"_line_00032">>)] IN
      /\ _frames' = _tmp_44
      /\ _pc' = _tmp_45
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00020_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00020_1")
  /\ (_actor = self)
  /\ LET _tmp_46 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
    /\ LET _tmp_47 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00017">>)] IN
      /\ _frames' = _tmp_46
      /\ _pc' = _tmp_47
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00022(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00022")
  /\ (_actor = self)
  /\ LET _tmp_48 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00017">>)] IN
    /\ _pc' = _tmp_48
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00017_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00017_1")
  /\ (_actor = self)
  /\ LET _tmp_49 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
    /\ LET _tmp_50 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
      /\ _frames' = _tmp_49
      /\ _pc' = _tmp_50
      /\ UNCHANGED _actor
      /\ UNCHANGED _globalsScratch
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00026(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00026")
  /\ (_actor = self)
  /\ \E _tmp_51 \in {_globalsScratch["head"]}:
    /\ LET _tmp_52 == _tmp_51 IN
      /\ LET _tmp_53 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _tmp_52) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
        /\ TRUE
        /\ LET _tmp_54 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00027">>)] IN
          /\ _frames' = _tmp_53
          /\ _pc' = _tmp_54
          /\ UNCHANGED _actor
          /\ UNCHANGED _globalsScratch
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00027(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00027")
  /\ (_actor = self)
  /\ LET _tmp_55 == _globalsScratch["head"] IN
    /\ LET _tmp_56 == _Undefined IN
      /\ LET _tmp_57 == _Undefined IN
        /\ LET _tmp_58 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00027_1">>)] IN
          /\ _actor' = _tmp_57
          /\ _globalsScratch' = _tmp_56
          /\ _pc' = _tmp_58
          /\ head' = _tmp_55
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_line_00027_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00027_1")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_59 == self IN
    /\ LET _tmp_60 == [head |-> head] IN
      /\ LET _tmp_61 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00028">>)] IN
        /\ _actor' = _tmp_59
        /\ _globalsScratch' = _tmp_60
        /\ _pc' = _tmp_61
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00028(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00028")
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
_line_00032(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00032")
  /\ (_actor = self)
  /\ LET _tmp_65 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_globalsScratch["head"] = _frames[self][Len(_frames[self])].expected) THEN "_line_00033" ELSE "_line_00037")>>)] IN
    /\ _pc' = _tmp_65
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00033(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00033")
  /\ (_actor = self)
  /\ \E _tmp_66 \in {_frames[self][Len(_frames[self])].new}:
    /\ LET _tmp_67 == _tmp_66 IN
      /\ LET _tmp_68 == [_globalsScratch EXCEPT !["head"] = _tmp_67] IN
        /\ TRUE
        /\ LET _tmp_69 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00034">>)] IN
          /\ _globalsScratch' = _tmp_68
          /\ _pc' = _tmp_69
          /\ UNCHANGED _actor
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
          /\ UNCHANGED head
_line_00034(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00034")
  /\ (_actor = self)
  /\ LET _tmp_70 == _globalsScratch["head"] IN
    /\ LET _tmp_71 == _Undefined IN
      /\ LET _tmp_72 == _Undefined IN
        /\ LET _tmp_73 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00034_1">>)] IN
          /\ _actor' = _tmp_72
          /\ _globalsScratch' = _tmp_71
          /\ _pc' = _tmp_73
          /\ head' = _tmp_70
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_line_00034_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00034_1")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_74 == self IN
    /\ LET _tmp_75 == [head |-> head] IN
      /\ LET _tmp_76 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00035">>)] IN
        /\ _actor' = _tmp_74
        /\ _globalsScratch' = _tmp_75
        /\ _pc' = _tmp_76
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00035(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00035")
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
_line_00037(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00037")
  /\ (_actor = self)
  /\ LET _tmp_80 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00037_1">>)] IN
    /\ _pc' = _tmp_80
    /\ UNCHANGED _actor
    /\ UNCHANGED _frames
    /\ UNCHANGED _globalsScratch
    /\ UNCHANGED _ret
    /\ UNCHANGED head
_line_00037_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00037_1")
  /\ (_actor = self)
  /\ LET _tmp_81 == _globalsScratch["head"] IN
    /\ LET _tmp_82 == _Undefined IN
      /\ LET _tmp_83 == _Undefined IN
        /\ LET _tmp_84 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00037_2">>)] IN
          /\ _actor' = _tmp_83
          /\ _globalsScratch' = _tmp_82
          /\ _pc' = _tmp_84
          /\ head' = _tmp_81
          /\ UNCHANGED _frames
          /\ UNCHANGED _ret
_line_00037_2(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00037_2")
  /\ TRUE
  /\ (_actor = _Undefined)
  /\ LET _tmp_85 == self IN
    /\ LET _tmp_86 == [head |-> head] IN
      /\ LET _tmp_87 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00038">>)] IN
        /\ _actor' = _tmp_85
        /\ _globalsScratch' = _tmp_86
        /\ _pc' = _tmp_87
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00038(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00038")
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
    \/ _line_00005(_pid)
    \/ _line_00006(_pid)
    \/ _line_00007(_pid)
    \/ _line_00008(_pid)
    \/ _line_00008_1(_pid)
    \/ _line_00009(_pid)
    \/ _line_00009_1(_pid)
    \/ _line_00007_1(_pid)
    \/ _line_00015(_pid)
    \/ _line_00016(_pid)
    \/ _line_00017(_pid)
    \/ _line_00018(_pid)
    \/ _line_00018_1(_pid)
    \/ _line_00019(_pid)
    \/ _line_00020(_pid)
    \/ _line_00020_1(_pid)
    \/ _line_00022(_pid)
    \/ _line_00017_1(_pid)
    \/ _line_00026(_pid)
    \/ _line_00027(_pid)
    \/ _line_00027_1(_pid)
    \/ _line_00028(_pid)
    \/ _line_00032(_pid)
    \/ _line_00033(_pid)
    \/ _line_00034(_pid)
    \/ _line_00034_1(_pid)
    \/ _line_00035(_pid)
    \/ _line_00037(_pid)
    \/ _line_00037_1(_pid)
    \/ _line_00037_2(_pid)
    \/ _line_00038(_pid)
    \/ _halt(_pid)
    \/ _begin_dequeue(_pid)
    \/ _begin_enqueue(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Stack.ezs

=====================
