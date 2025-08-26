⊢ s.net[↑node].length <
  (
    
    (Vector.set
            (foldSharers
                (List.filter
                  (fun shim ↦
                    !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                      (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! && !decide (↑shim = ↑c.threads)))
                  (List.finRange (↑c.threads + 1)))
                s.net[↑c.threads].head! s.net s.msgIds
                {
                  cache :=
                    Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                      { data := s.net[↑c.threads].head!.data, ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                        sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                      ⋯ }).1
            (↑s.net[↑c.threads].head!.src)
            ((foldSharers
                    (List.filter
                      (fun shim ↦
                        !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                          (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! && !decide (↑shim = ↑c.threads)))
                      (List.finRange (↑c.threads + 1)))
                    s.net[↑c.threads].head! s.net s.msgIds
                    {
                      cache :=
                        Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                          { data := s.net[↑c.threads].head!.data,
                            ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                            sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                          ⋯ }).1[↑s.net[↑c.threads].head!.src] ++
              [{ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, ⋯⟩, dst := s.net[↑c.threads].head!.src,
                  data := s.net[↑c.threads].head!.data, addr := s.net[↑c.threads].head!.addr,
                  ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1, stren := s.net[↑c.threads].head!.stren,
                  id :=
                    (foldSharers
                          (List.filter
                            (fun shim ↦
                              !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                                (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! &&
                                  !decide (↑shim = ↑c.threads)))
                            (List.finRange (↑c.threads + 1)))
                          s.net[↑c.threads].head! s.net s.msgIds
                          {
                            cache :=
                              Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                                { data := s.net[↑c.threads].head!.data,
                                  ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                                  sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                                ⋯ }).2[↑s.net[↑c.threads].head!.src] }])
            ⋯).set


        (↑c.threads)


        ((Vector.set
              (foldSharers
                  (List.filter
                    (fun shim ↦
                      !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                        (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! && !decide (↑shim = ↑c.threads)))
                    (List.finRange (↑c.threads + 1)))
                  s.net[↑c.threads].head! s.net s.msgIds
                  {
                    cache :=
                      Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                        { data := s.net[↑c.threads].head!.data, ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                          sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                        ⋯ }).1
              (↑s.net[↑c.threads].head!.src)
              ((foldSharers
                      (List.filter
                        (fun shim ↦
                          !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                            (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! && !decide (↑shim = ↑c.threads)))
                        (List.finRange (↑c.threads + 1)))
                      s.net[↑c.threads].head! s.net s.msgIds
                      {
                        cache :=
                          Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                            { data := s.net[↑c.threads].head!.data,
                              ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                              sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                            ⋯ }).1[↑s.net[↑c.threads].head!.src] ++
                [{ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, ⋯⟩, dst := s.net[↑c.threads].head!.src,
                    data := s.net[↑c.threads].head!.data, addr := s.net[↑c.threads].head!.addr,
                    ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1, stren := s.net[↑c.threads].head!.stren,
                    id :=
                      (foldSharers
                            (List.filter
                              (fun shim ↦
                                !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                                  (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! &&
                                    !decide (↑shim = ↑c.threads)))
                              (List.finRange (↑c.threads + 1)))
                            s.net[↑c.threads].head! s.net s.msgIds
                            {
                              cache :=
                                Vector.set s.cc.cache ↑s.net[↑c.threads].head!.addr
                                  { data := s.net[↑c.threads].head!.data,
                                    ts := s.cc.cache[↑s.net[↑c.threads].head!.addr].ts + 1,
                                    sharers := s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers }
                                  ⋯ }).2[↑s.net[↑c.threads].head!.src] }])
              ⋯)[↑c.threads].tail)


        ⋯)[↑node].length