%div_t = type { i64, i64 }

define void @div(%div_t* %result, i64 %numer, i64 %denom) {
  %quot = alloca i64
  %rem = alloca i64
  store i64 0, i64* %quot
  store i64 %numer, i64* %rem
  br label %start

start:
  %1 = load i64, i64* %rem
  %2 = icmp sge i64 %1, %denom
  br i1 %2, label %loop, label %end

loop:
  %3 = load i64, i64* %rem
  %4 = sub i64 %3, %denom
  store i64 %4, i64* %rem

  %5 = load i64, i64* %quot
  %6 = add i64 %5, 1
  store i64 %6, i64* %quot

  br label %start

end:
  %7 = load i64, i64* %quot
  %8 = getelementptr %div_t, %div_t* %result, i32 0, i32 0
  store i64 %7, i64* %8

  %9 = load i64, i64* %rem
  %10 = getelementptr %div_t, %div_t* %result, i32 0, i32 1
  store i64 %9, i64* %10

  ret void
}

@magic = global [14 x i8] c"-bed=pen+mad.\00"

define i64 @day_of_the_week(i64 %year, i64 %month, i64 %day) {
  %result = alloca i64
  %div_result = alloca %div_t

  %1 = icmp slt i64 %month, 3
  %2 = sub i64 %year, %1

  %y = alloca i64
  store i64 %2, i64* %y

  store i64 %y, i64* %result

  call void @div(%div_t* %div_result, i64 %y, i64 4)
  %3 = getelementptr %div_t, %div_t* %div_result, i32 0, i32 0
  %4 = load i64, i64* %3
  %5 = load i64, i64* %result
  %6 = add i64 %5, %4
  store i64 %6, i64* %result

  call void @div(%div_t* %div_result, i64 %y, i64 100)
  %7 = getelementptr %div_t, %div_t* %div_result, i32 0, i32 0
  %8 = load i64, i64* %7
  %9 = load i64, i64* %result
  %10 = sub i64 %9, %8
  store i64 %10, i64* %result

  call void @div(%div_t* %div_result, i64 %y, i64 400)
  %11 = getelementptr %div_t, %div_t* %div_result, i32 0, i32 0
  %12 = load i64, i64* %11
  %13 = load i64, i64* %result
  %14 = add i64 %13, %12
  store i64 %14, i64* %result

  %15 = getelementptr [14 x i8], [14 x i8]* @magic, i32 0, i64 %month
  %16 = load i8, i8* %15
  %17 = load i64, i64* %result
  %18 = add i64 %17, %16
  store i64 %18, i64* %result

  %19 = load i64, i64* %result
  %20 = add i64 %19, %day
  store i64 %20, i64* %result

  call void @div(%div_t* %div_result, i64 %result, i64 7)
  %21 = getelementptr %div_t, %div_t* %div_result, i32 0, i32 1
  ret i64 %21
}

define i64 @main(i64 %argc, i8** %argv) {
  %result = call i64 @day_of_the_week(i64 2024, i64 11, i64 4)
  ret i64 %result
}
