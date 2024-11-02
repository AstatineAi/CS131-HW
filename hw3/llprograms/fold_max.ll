@arr = global [10 x i64] [i64 1, i64 4, i64 1, i64 2, i64 2, i64 5, i64 2, i64 3, i64 8, i64 1]
@arrlen = global i64 10

define i64 @fold(i64(i64, i64)* %f, i64 %acc, [10 x i64]* %arr, i64 %arridx, i64 %len) {
  %end = icmp eq i64 %len, %arridx
  br i1 %end, label %return, label %recurse
recurse:
  %hptr = getelementptr [10 x i64], [10 x i64]* %arr, i64 0, i64 %arridx
  %head = load i64, i64* %hptr
  %newacc = call i64 %f(i64 %acc, i64 %head)
  %newidx = add i64 %arridx, 1
  %res = call i64 @fold(i64(i64, i64)* %f, i64 %newacc, [10 x i64]* %arr, i64 %newidx, i64 %len)
  ret i64 %res
return:
  ret i64 %acc
}

define i64 @max(i64 %a, i64 %b) {
  %cmp = icmp sgt i64 %a, %b
  br i1 %cmp, label %a, label %b
a:
  ret i64 %a
b:
  ret i64 %b
}

define i64 @main(i64 %argc, i8** %argv) {
  %len = load i64, i64* @arrlen
  %res = call i64 @fold(i64(i64, i64)* @max, i64 -114514, [10 x i64]* @arr, i64 0, i64 %len)
  ret i64 %res
}
