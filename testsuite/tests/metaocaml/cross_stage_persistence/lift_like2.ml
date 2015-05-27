let f a = .<a>. in
   (.! (f (fun () -> "Hello"))) ();;
