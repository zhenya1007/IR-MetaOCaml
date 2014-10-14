let c =
  let r = ref 5 in
  let f a = .<a>. in
  f r;;
Gc.compact ();;
!(.! c);;
