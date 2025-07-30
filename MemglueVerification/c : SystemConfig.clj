c : SystemConfig
s s' : IncState c
shim : ShimId c
h_issue : canIssueInstr shim s
h_s' : s' = getAndIssueInstr shim s
h_W : (getInstr shim s.shimVec s.execution).2.access = PermissionType.store
h_step : increment_step s s'
h✝ : ¬(getInstr shim s.shimVec s.execution).2.stren = OpStrength.SC
⊢ (Vector.get
      
      ;; below is `s'.shimVec` from the increments_ts definition, we're updating shim
      ((Vector.set (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 ↑shim
              {
                state :=
                  Vector.set (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).state
                    ↑(getInstr shim s.shimVec s.execution).2.addr
                    { state := CacheState.Valid, data := (getInstr shim s.shimVec s.execution).2.data,
                      ts :=
                        (Vector.get (Vector.get s.shimVec shim).state (getInstr shim s.shimVec s.execution).2.addr).ts +
                          1,
                      syncBit :=
                        (Vector.get
                            (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).state
                            (getInstr shim s.shimVec s.execution).2.addr).syncBit }
                    ⋯,
                active := (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).active,
                pendingWSC :=
                  (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).pendingWSC,
                fencePending :=
                  (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).fencePending,
                qInd := (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).qInd,
                qCnt := (Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).qCnt }
              ⋯)
              
              .get
          shim).state
      (getInstr shim s.shimVec s.execution).2.addr).ts =
  (Vector.get (Vector.get s.shimVec shim).state (getInstr shim s.shimVec s.execution).2.addr).ts + 1


;; new goal after I changed ShimType from a Vector to a List.Vector
⊢ ((Vector.set (List.Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).state
          ↑(getInstr shim s.shimVec s.execution).2.addr
          { state := CacheState.Valid, data := (getInstr shim s.shimVec s.execution).2.data,
            ts :=
              (Vector.get (List.Vector.get s.shimVec shim).state (getInstr shim s.shimVec s.execution).2.addr).ts + 1,
            syncBit :=
              (Vector.get
                  (List.Vector.get (popInstr shim s.shimVec (getInstr shim s.shimVec s.execution).1).1 shim).state
                  (getInstr shim s.shimVec s.execution).2.addr).syncBit }
          ⋯).get
      (getInstr shim s.shimVec s.execution).2.addr).ts =
  (Vector.get (List.Vector.get s.shimVec shim).state (getInstr shim s.shimVec s.execution).2.addr).ts + 1