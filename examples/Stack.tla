---- MODULE Stack ----

EXTENDS Integers, Sequences, TLC

CONSTANT Null

\* #include Stack.ezs
CONSTANTS _Undefined, dequeue_calls, enqueue_calls
VARIABLES _pc, _frames, _ret, _actor, head
vars == <<_pc, _frames, _ret, _actor, head>>
symmetry == UNION {Permutations(dequeue_calls), Permutations(enqueue_calls)}
Init ==
  /\ _pc = [_pid \in dequeue_calls |-> <<"_dequeue">>] @@ [_pid \in enqueue_calls |-> <<"_enqueue">>]
  /\ _frames = [_pid \in dequeue_calls |-> << <<>> >>] @@ [_pid \in enqueue_calls |-> << <<>> >>]
  /\ _ret = [_pid \in dequeue_calls |-> _Undefined] @@ [_pid \in enqueue_calls |-> _Undefined]
  /\ _actor = _Undefined
  /\ head = Null
_CAS(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_CAS")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp == self IN
    /\ LET _tmp_1 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (head = _frames[self][Len(_frames[self])].expected) THEN "_line_00034" ELSE "_line_00038")>>)] IN
      /\ _actor' = _tmp
      /\ _pc' = _tmp_1
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_dequeue(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_dequeue")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_2 == self IN
    /\ LET _tmp_3 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> Null) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_4 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00017">>)] IN
        /\ _actor' = _tmp_2
        /\ _frames' = _tmp_3
        /\ _pc' = _tmp_4
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_enqueue(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_enqueue")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_5 == self IN
    /\ LET _tmp_6 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> Null) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_7 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00007">>)] IN
        /\ _actor' = _tmp_5
        /\ _frames' = _tmp_6
        /\ _pc' = _tmp_7
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00007(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_8 == self IN
    /\ LET _tmp_9 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> FALSE) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_10 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00011">>)] IN
        /\ _actor' = _tmp_8
        /\ _frames' = _tmp_9
        /\ _pc' = _tmp_10
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00009(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_11 == self IN
    /\ LET _tmp_12 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
      /\ LET _tmp_13 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00009_1">>) \o <<"_read">>)] IN
        /\ _actor' = _tmp_11
        /\ _frames' = _tmp_12
        /\ _pc' = _tmp_13
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00009_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00009_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_14 == self IN
    /\ LET _tmp_15 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_16 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00010">>)] IN
        /\ _actor' = _tmp_14
        /\ _frames' = _tmp_15
        /\ _pc' = _tmp_16
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00010(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00010")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_17 == self IN
    /\ LET _tmp_18 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> [value |-> self, next |-> _frames[self][Len(_frames[self])].tmp]]>>)] IN
      /\ LET _tmp_19 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00010_1">>) \o <<"_CAS">>)] IN
        /\ _actor' = _tmp_17
        /\ _frames' = _tmp_18
        /\ _pc' = _tmp_19
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00010_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00010_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_20 == self IN
    /\ LET _tmp_21 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_22 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00013">>)] IN
        /\ _actor' = _tmp_20
        /\ _frames' = _tmp_21
        /\ _pc' = _tmp_22
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00011(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00011")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_23 == self IN
    /\ LET _tmp_24 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_line_00009" ELSE "_line_00013")>>)] IN
      /\ _actor' = _tmp_23
      /\ _pc' = _tmp_24
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00013(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00013")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_25 == self IN
    /\ LET _tmp_26 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_27 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_28 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_25
          /\ _frames' = _tmp_27
          /\ _pc' = _tmp_28
          /\ _ret' = _tmp_26
          /\ UNCHANGED head
_line_00017(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00017")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_29 == self IN
    /\ LET _tmp_30 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> FALSE) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_31 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00023">>)] IN
        /\ _actor' = _tmp_29
        /\ _frames' = _tmp_30
        /\ _pc' = _tmp_31
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00019(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00019")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_32 == self IN
    /\ LET _tmp_33 == [_frames EXCEPT ![self] = (_frames[self] \o <<<<>>>>)] IN
      /\ LET _tmp_34 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00019_1">>) \o <<"_read">>)] IN
        /\ _actor' = _tmp_32
        /\ _frames' = _tmp_33
        /\ _pc' = _tmp_34
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00019_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00019_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_35 == self IN
    /\ LET _tmp_36 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_37 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00022">>)] IN
        /\ _actor' = _tmp_35
        /\ _frames' = _tmp_36
        /\ _pc' = _tmp_37
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00021(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00021")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_38 == self IN
    /\ LET _tmp_39 == [_frames EXCEPT ![self] = (_frames[self] \o <<[expected |-> _frames[self][Len(_frames[self])].tmp, new |-> _frames[self][Len(_frames[self])].tmp.next]>>)] IN
      /\ LET _tmp_40 == [_pc EXCEPT ![self] = ((SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00021_1">>) \o <<"_CAS">>)] IN
        /\ _actor' = _tmp_38
        /\ _frames' = _tmp_39
        /\ _pc' = _tmp_40
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00021_1(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00021_1")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_41 == self IN
    /\ LET _tmp_42 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("success" :> _ret[self]) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_43 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00025">>)] IN
        /\ _actor' = _tmp_41
        /\ _frames' = _tmp_42
        /\ _pc' = _tmp_43
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00022(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00022")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_44 == self IN
    /\ LET _tmp_45 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF (_frames[self][Len(_frames[self])].tmp /= Null) THEN "_line_00021" ELSE "_line_00025")>>)] IN
      /\ _actor' = _tmp_44
      /\ _pc' = _tmp_45
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00023(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00023")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_46 == self IN
    /\ LET _tmp_47 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<(IF ~_frames[self][Len(_frames[self])].success THEN "_line_00019" ELSE "_line_00025")>>)] IN
      /\ _actor' = _tmp_46
      /\ _pc' = _tmp_47
      /\ UNCHANGED _frames
      /\ UNCHANGED _ret
      /\ UNCHANGED head
_line_00025(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00025")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_48 == self IN
    /\ LET _tmp_49 == [_ret EXCEPT ![self] = _Undefined] IN
      /\ LET _tmp_50 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_51 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_48
          /\ _frames' = _tmp_50
          /\ _pc' = _tmp_51
          /\ _ret' = _tmp_49
          /\ UNCHANGED head
_line_00028(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00028")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_52 == self IN
    /\ LET _tmp_53 == _Undefined IN
      /\ LET _tmp_54 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00029">>)] IN
        /\ _actor' = _tmp_53
        /\ _pc' = _tmp_54
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00029(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00029")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_55 == self IN
    /\ LET _tmp_56 == [_ret EXCEPT ![self] = _frames[self][Len(_frames[self])].tmp] IN
      /\ LET _tmp_57 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_58 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_55
          /\ _frames' = _tmp_57
          /\ _pc' = _tmp_58
          /\ _ret' = _tmp_56
          /\ UNCHANGED head
_line_00034(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00034")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_59 == self IN
    /\ LET _tmp_60 == _frames[self][Len(_frames[self])].new IN
      /\ LET _tmp_61 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00035">>)] IN
        /\ _actor' = _tmp_59
        /\ _pc' = _tmp_61
        /\ head' = _tmp_60
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
_line_00035(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00035")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_62 == self IN
    /\ LET _tmp_63 == _Undefined IN
      /\ LET _tmp_64 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00036">>)] IN
        /\ _actor' = _tmp_63
        /\ _pc' = _tmp_64
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00036(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00036")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_65 == self IN
    /\ LET _tmp_66 == [_ret EXCEPT ![self] = TRUE] IN
      /\ LET _tmp_67 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_68 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_65
          /\ _frames' = _tmp_67
          /\ _pc' = _tmp_68
          /\ _ret' = _tmp_66
          /\ UNCHANGED head
_line_00038(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00038")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_69 == self IN
    /\ LET _tmp_70 == _Undefined IN
      /\ LET _tmp_71 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00039">>)] IN
        /\ _actor' = _tmp_70
        /\ _pc' = _tmp_71
        /\ UNCHANGED _frames
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_line_00039(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_line_00039")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_72 == self IN
    /\ LET _tmp_73 == [_ret EXCEPT ![self] = FALSE] IN
      /\ LET _tmp_74 == [_frames EXCEPT ![self] = SubSeq(_frames[self], 1, (Len(_frames[self]) - 1))] IN
        /\ LET _tmp_75 == [_pc EXCEPT ![self] = SubSeq(_pc[self], 1, (Len(_pc[self]) - 1))] IN
          /\ _actor' = _tmp_72
          /\ _frames' = _tmp_74
          /\ _pc' = _tmp_75
          /\ _ret' = _tmp_73
          /\ UNCHANGED head
_read(self) ==
  /\ (Len(_pc[self]) > 0)
  /\ (_pc[self][Len(_pc[self])] = "_read")
  /\ ((_actor = _Undefined) \/ (_actor = self))
  /\ LET _tmp_76 == self IN
    /\ LET _tmp_77 == [_frames EXCEPT ![self] = ((Len(_frames[self]) :> (("tmp" :> head) @@ _frames[self][Len(_frames[self])])) @@ _frames[self])] IN
      /\ LET _tmp_78 == [_pc EXCEPT ![self] = (SubSeq(_pc[self], 1, (Len(_pc[self]) - 1)) \o <<"_line_00028">>)] IN
        /\ _actor' = _tmp_76
        /\ _frames' = _tmp_77
        /\ _pc' = _tmp_78
        /\ UNCHANGED _ret
        /\ UNCHANGED head
_halt(self) ==
  /\ _pc[self] = <<>>
  /\ _actor = self
  /\ _actor' = _Undefined
  /\ _ret' = [_ret EXCEPT ![self] = _Undefined]
  /\ UNCHANGED _frames
  /\ UNCHANGED _pc
  /\ UNCHANGED head
\* `_finished` prevents TLC from reporting deadlock when all processes finish normally
_finished ==
  /\ \A self \in UNION {dequeue_calls, enqueue_calls}: _pc[self] = <<>>
  /\ UNCHANGED <<_pc, _frames, _ret, _actor, head>>
Next ==
  \E _pid \in UNION {dequeue_calls, enqueue_calls}:
    \/ _CAS(_pid)
    \/ _dequeue(_pid)
    \/ _enqueue(_pid)
    \/ _line_00007(_pid)
    \/ _line_00009(_pid)
    \/ _line_00009_1(_pid)
    \/ _line_00010(_pid)
    \/ _line_00010_1(_pid)
    \/ _line_00011(_pid)
    \/ _line_00013(_pid)
    \/ _line_00017(_pid)
    \/ _line_00019(_pid)
    \/ _line_00019_1(_pid)
    \/ _line_00021(_pid)
    \/ _line_00021_1(_pid)
    \/ _line_00022(_pid)
    \/ _line_00023(_pid)
    \/ _line_00025(_pid)
    \/ _line_00028(_pid)
    \/ _line_00029(_pid)
    \/ _line_00034(_pid)
    \/ _line_00035(_pid)
    \/ _line_00036(_pid)
    \/ _line_00038(_pid)
    \/ _line_00039(_pid)
    \/ _read(_pid)
    \/ _halt(_pid)
    \/ _finished
NoAssertionFailures == TRUE
\* /include Stack.ezs

=====================
