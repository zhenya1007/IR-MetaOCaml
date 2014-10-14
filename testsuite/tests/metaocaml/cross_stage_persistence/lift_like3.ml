let r = ref 4 in
let f a = .<a>. in
let () = (.! (f (fun () -> r := 5))) () in
!r ;;
