; Test that bugpoint can narrow down the testcase to the important function
;
; RUN: bugpoint -load %llvmshlibdir/BugpointPasses%shlibext %s -output-prefix %t -bugpoint-crashcalls -silence-passes -mlimit=0 > /dev/null
; REQUIRES: loadable_module

define i32 @foo() { ret i32 1 }

define i32 @test() {
	call i32 @test()
	ret i32 %1
}

define i32 @bar() { ret i32 2 }
