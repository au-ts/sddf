; Copyright 2026, UNSW
; SPDX-License-Identifier: BSD-2-Clause

; Improvements (TODO)
; - Make the proof about period_shift generic, instead of two instantiations
;   one for ticks2ns and ns2ticks with duplicated internals.
; - Link more closely to C code.

(set-option :produce-unsat-cores true)

(declare-const GHz Int)
(assert (= GHz 1000000000))

(define-fun precise_period_shift ((period Int) (target_freq Int) (input_freq Int)) Real
    (/ (* period target_freq) input_freq))

(define-fun precise_ticks_to_ns ((ticks Int) (freq Int)) Real
    (precise_period_shift ticks (* 1 GHz) freq))

(define-fun precise_ns_to_ticks ((ns Int) (freq Int)) Real
    (precise_period_shift ns freq (* 1 GHz)))

; TODO: this really should be "rounded" and allows a bit more slack than we really should but
; compare some integer b to floating point xxx.yyy and check if it is xxx or xxx + 1
(define-fun real_is_within_unit_distance ((a Real) (b Int)) Bool
    ; either: b == a, or b < a < b + 1, or b - 1 < a < b
    (or
        ; b == a
        (= b a)
        ; b < a < b + 1
        (<= b a (+ b 1))
        (<= (- b 1) a b)
    ))

(define-fun is_64_bit_int ((x Int)) Bool (<= 0 x 18446744073709551615))
(define-fun is_61_bit_int ((x Int)) Bool (<= 0 x 2305843009213693951))
(define-fun is_48_bit_int ((x Int)) Bool (<= 0 x 281474976710655))
(define-fun is_32_bit_int ((x Int)) Bool (<= 0 x 4294967295))

(push)
    (echo "=== precise_ticks_to_ns test")
    (declare-const ns Int)
    (declare-const ticks Int)
    (assert (= ticks 2))
    ; 2 ticks at 1Hz is = 2e9 nanoseconds
    (assert (= ns (precise_ticks_to_ns ticks 1)))
    (assert (= ns 2000000000))
    (check-sat)
    ; (get-model)
(pop)

(push)
    (echo "=== precise_ns_to_ticks test")
    (declare-const ns Int)
    (declare-const ticks Int)
    (assert (= ns 2000000000))
    ; 2e9 nanoseconds at 1Hz is 2 ticks
    (assert (= ticks (precise_ns_to_ticks ns 1)))
    (assert (= ticks 2))
    (check-sat)
    ; (get-model)
(pop)


(push)
    (echo "=== sDDF ticks to ns (unsat is proof; sat shows a counterexample)")
    ; Corresponds to ticks2ns(ticks, freq) which calls period_shift(ticks, 1 GHz, freq)
    ; Due to limitations of this smtlib language we have to inline the definitions of both.

    (declare-const freq Int)
    (declare-const ticks Int)
    (declare-const ns_precise Real)
    (declare-const ns_sddf   Int)

    ; 1 <= freq <= 2^32 - 1 (~ 4GHz)
    (assert (is_32_bit_int freq))
    (assert (not (= freq 0)))
    ; 0 <= ... <= 2^64 - 1
    (assert (is_64_bit_int ticks)); by input

    (assert (
        ; note log base 2
        ; log(out_period_whole) = log(period) + (log(target_freq) - log(input_freq))
        ; log(out_period_whole) < 64
        ; log(period) + log(target_freq) - log(input_freq) < 64
        ; log(period) - log(input_freq) < 64 - log(target_freq)
        ;
        ; For ticks2ns; period = ticks, input_freq = freq, target_freq = 10^9
        ;
        ;     log(ticks) - log(freq) < 64 - log(10^9)
        ; 2^(log(ticks) - log(freq)) < 2^(64 - log(10^9))
        ;               ticks / freq < 2^(64 - log(10^9))
        ;                            < 18446744073.70953
        ;
        <= 0.0 (/ ticks freq) 18446744073
        ; gives sat
        ; <= 0.0 (/ ticks freq) 18446744074

        ; for freq 1MHz we get ~1.8e7 ~ 200 days
        ; for freq 1Ghz we get ~1.8e10 ~ 600 years
    ))

    ; This is the oracle done in z3's 'Real' (i.e. rational) numbers
    (assert (= ns_precise (precise_ticks_to_ns ticks freq)))

    ; The arguments to period_shift.
    (declare-const period Int)
    (assert (= period ticks))
    (declare-const input_freq Int)
    (assert (= input_freq freq))
    (declare-const target_freq Int)
    (assert (= target_freq (* 1 GHz)))
    (declare-const out_period Int)
    (assert (= out_period ns_sddf))

    (declare-const period_whole Int)
    (declare-const out_period_whole Int)
    (declare-const period_remainder Int)
    (declare-const out_period_remainder_intermediate Int)
    (declare-const out_period_remainder Int)

    ; C: `uint64_t out_period_whole = (period / input_freq) * target_freq`
    ; log(period_whole) = log(period) - log(input_freq).
    ; No overflow, just truncation.
    (assert (= period_whole (/ period input_freq)))
    ; log(out_period_whole) = log(period_whole) + log(target_freq) = log(period) + (log(target_freq) - log(input_freq))
    ; No overflow if input_freq <= target_freq. Permissible overflow (out of range input) otherwise.
    (assert (= out_period_whole (* period_whole target_freq)))

    ; C: `uint64_t period_remainder = period % input_freq`.
    ; log(period_remainder) <= log(input_freq)
    (assert (= period_remainder (rem period input_freq)))

    ; C: `uint64_t out_period_remainder = (period_remainder * target_freq) / input_freq;`
    ; log(out_period_remainder_intermediate) = log(period_remainder) + log(target_freq)
    ;                                        <= log(input_freq) + log(target_freq)
    ; No overflow if input_freq * target_freq is <= 2^64. Non-permissible overflow otherwise.
    (assert (= out_period_remainder_intermediate (* period_remainder target_freq)))
    ; log(out_period_remainder) = log(out_period_remainder_intermediate) - log(input_freq).
    ; No overflow, just truncation.
    (assert (= out_period_remainder (/ out_period_remainder_intermediate input_freq)))

    ; C: `return out_period_whole + out_period_remainder;`
    ; As remainder < whole, permissible overflow (out of range input) only when near 2^64 input.
    (assert (= out_period (+ out_period_whole out_period_remainder)))

    (
        assert
        (
            or
            (not (is_64_bit_int period_whole))
            (not (is_64_bit_int out_period_whole))
            (not (is_64_bit_int period_remainder))
            (not (is_64_bit_int out_period_remainder_intermediate))
            (not (is_64_bit_int out_period_remainder))
            (not (is_64_bit_int out_period))
            (not (real_is_within_unit_distance ns_precise ns_sddf))
        )
    )

    (check-sat)
    ; (get-model)
    ; (get-unsat-core)
(pop)

(push)
    (echo "=== sDDF ns to ticks (unsat is proof; sat shows a counterexample)")
    ; Corresponds to ns2ticks(ticks, freq) which calls period_shift(ticks, freq, 1 GHz)
    ; Due to limitations of this smtlib language we have to inline the definitions of both.

    (declare-const freq Int)
    (declare-const ns Int)
    (declare-const ticks_precise Real)
    (declare-const ticks_sddf   Int)

    ; 1 <= freq <= 2^32 - 1 (~ 4GHz)
    (assert (is_32_bit_int freq))
    (assert (not (= freq 0)))
    ; 0 <= ... <= 2^64 - 1
    (assert (is_64_bit_int ns)); by input

    (assert (
        ; note log base 2
        ; log(out_period_whole) = log(period) + (log(target_freq) - log(input_freq))
        ; log(out_period_whole) < 64
        ; log(period) + log(target_freq) - log(input_freq) < 64
        ; log(period) - log(input_freq) < 64 - log(target_freq)
        ;
        ; For ns2ticks; period = ns, input_freq = 10^9, target_freq = freq
        ;
        ;     log(ns) - log(10^9) < 64 - log(freq)
        ;     log(ns) - log(10^9) < 64 - log(freq)
        ; 2^(log(ns) - log(10^9)) < 2^(64 - log(freq))
        ;               ns / 10^9 < 2^64 / freq
        ;
        ; Alternative form that requires >64 bits to evaluate:
        ;               ns * freq < 2^64 * 10^9
        ; (useful for z3 to prove tightest bound)
        ;
        < (div ns 1000000000) (div 18446744073709551616 freq)
        ; < (* ns freq) 18446744073709551616000000000
        ; This times out, so z3 can't prove it works.
        ; < (* ns freq) 18446744073709551616000000001
    ))

    ; This is the oracle done in z3's 'Real' (i.e. rational) numbers
    (assert (= ticks_precise (precise_ns_to_ticks ns freq)))

    ; The arguments to period_shift. Note this is swapped compared to ticks2ns
    (declare-const period Int)
    (assert (= period ns))
    (declare-const input_freq Int)
    (assert (= input_freq (* 1 GHz)))
    (declare-const target_freq Int)
    (assert (= target_freq freq))
    (declare-const out_period Int)
    (assert (= out_period ticks_sddf))

    (declare-const period_whole Int)
    (declare-const out_period_whole Int)
    (declare-const period_remainder Int)
    (declare-const out_period_remainder_intermediate Int)
    (declare-const out_period_remainder Int)

    ; C: `uint64_t out_period_whole = (period / input_freq) * target_freq`
    ; log(period_whole) = log(period) - log(input_freq).
    ; No overflow, just truncation.
    (assert (= period_whole (/ period input_freq)))
    ; log(out_period_whole) = log(period_whole) + log(target_freq) = log(period) + (log(target_freq) - log(input_freq))
    ; No overflow if input_freq <= target_freq. Permissible overflow (out of range input) otherwise.
    (assert (= out_period_whole (* period_whole target_freq)))

    ; C: `uint64_t period_remainder = period % input_freq`.
    ; log(period_remainder) <= log(input_freq)
    (assert (= period_remainder (rem period input_freq)))

    ; C: `uint64_t out_period_remainder = (period_remainder * target_freq) / input_freq;`
    ; log(out_period_remainder_intermediate) = log(period_remainder) + log(target_freq)
    ;                                        <= log(input_freq) + log(target_freq)
    ; No overflow if input_freq * target_freq is <= 2^64. Non-permissible overflow otherwise.
    (assert (= out_period_remainder_intermediate (* period_remainder target_freq)))
    ; log(out_period_remainder) = log(out_period_remainder_intermediate) - log(input_freq).
    ; No overflow, just truncation.
    (assert (= out_period_remainder (/ out_period_remainder_intermediate input_freq)))

    ; C: `return out_period_whole + out_period_remainder;`
    ; As remainder < whole, permissible overflow (out of range input) only when near 2^64 input.
    (assert (= out_period (+ out_period_whole out_period_remainder)))

    (
        assert
        (
            or
            (not (is_64_bit_int period_whole))
            (not (is_64_bit_int out_period_whole))
            (not (is_64_bit_int period_remainder))
            (not (is_64_bit_int out_period_remainder_intermediate))
            (not (is_64_bit_int out_period_remainder))
            (not (is_64_bit_int out_period))
            (not (real_is_within_unit_distance ticks_precise ticks_sddf))
        )
    )

    (check-sat)
    ; (get-model)
    ; (get-unsat-core)
(pop)
