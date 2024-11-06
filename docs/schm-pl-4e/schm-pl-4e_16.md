# 形式总结

下表总结了在第四章至第十一章中描述的 Scheme 语法形式和过程。它显示了形式的类别以及定义该形式的页码。类别说明该形式是描述语法形式还是过程。

所有出现在这里的页码均指向本书的印刷版本，并同时作为本书电子版本中相应位置的超文本链接。

| 形式 | 类别 | 页码 |
| --- | --- | --- |

|

* * *

|

| `'*obj*` | 语法 | 141 |
| --- | --- | --- |
| ``*obj*` | 语法 | 142 |
| `,*obj*` | 语法 | 142 |
| `,@*obj*` | 语法 | 142 |
| `=>` | 语法 | 112 |
| `_` | 语法 | 297 |
| `...` | 语法 | 297 |
| `#'*template*` | 语法 | 300 |
| `#`*template*` | 语法 | 305 |
| `#,*template*` | 语法 | 305 |
| `#,@*template*` | 语法 | 305 |
| `&assertion` | 语法 | 366 |
| `&condition` | 语法 | 362 |
| `&error` | 语法 | 367 |
| `&i/o` | 语法 | 371 |
| `&i/o-decoding` | 语法 | 375 |
| `&i/o-encoding` | 语法 | 376 |
| `&i/o-file-already-exists` | 语法 | 374 |
| `&i/o-file-does-not-exist` | ��法 | 374 |
| `&i/o-file-is-read-only` | 语法 | 374 |
| `&i/o-file-protection` | 语法 | 373 |
| `&i/o-filename` | 语法 | 373 |
| `&i/o-invalid-position` | 语法 | 372 |
| `&i/o-port` | 语法 | 375 |
| `&i/o-read` | 语法 | 372 |
| `&i/o-write` | 语法 | 372 |
| `&implementation-restriction` | 语法 | 369 |
| `&irritants` | 语法 | 368 |
| `&lexical` | 语法 | 370 |
| `&message` | 语法 | 368 |
| `&no-infinities` | 语法 | 376 |
| `&no-nans` | 语法 | 377 |
| `&non-continuable` | 语法 | 369 |
| `&serious` | 语法 | 366 |
| `&syntax` | 语法 | 370 |
| `&undefined` | 语法 | 371 |
| `&violation` | 语法 | 366 |
| `&warning` | 语法 | 367 |
| `&who` | 语法 | 369 |
| `(* *num* ...)` | 过程 | 172 |
| `(+ *num* ...)` | 过程 | 171 |
| `(- *num*)` | 过程 | 172 |
| `(- *num[1]* *num[2]* *num[3]* ...)` | 过程 | 172 |
| `(/ *num*)` | 过程 | 172 |
| `(/ *num[1]* *num[2]* *num[3]* ...)` | 过程 | 172 |
| `(< *real[1]* *real[2]* *real[3]* ...)` | 过程 | 170 |
| `(<= *real[1]* *real[2]* *real[3]* ...)` | 过程 | 170 |
| `(= *num[1]* *num[2]* *num[3]* ...)` | 过程 | 170 |
| `(> *real[1]* *real[2]* *real[3]* ...)` | 过程 | 170 |
| `(>= *real[1]* *real[2]* *real[3]* ...)` | 过程 | 170 |
| `(abs *real*)` | 过程 | 178 |
| `(acos *num*)` | 过程 | 185 |
| `(and *expr* ...)` | 语法 | 110 |
| `(angle *num*)` | 过程 | 183 |
| `(append)` | 过程 | 160 |
| `(append *list* ... *obj*)` | 过程 | 160 |
| `(apply *procedure* *obj* ... *list*)` | 过程 | 107 |
| `(asin *num*)` | 过程 | 185 |
| `(assert *expression*)` | 语法 | 359 |
| `(assertion-violation *who* *msg* *irritant* ...)` | 过程 | 358 |
| `(assertion-violation? *obj*)` | 过程 | 366 |
| `(assoc *obj* *alist*)` | 过程 | 165 |
| `(assp *procedure* *alist*)` | 过程 | 166 |
| `(assq *obj* *alist*)` | 过程 | 165 |
| `(assv *obj* *alist*)` | 过程 | 165 |
| `(atan *num*)` | 过程 | 185 |
| `(atan *real[1]* *real[2]*)` | 过程 | 185 |
| `(begin *expr[1]* *expr[2]* ...)` | 语法 | 108 |
| `(binary-port? *obj*)` | 过程 | 270 |
| `(bitwise-and *exint* ...)` | 过程 | 186 |
| `(bitwise-arithmetic-shift *exint[1]* *exint[2]*)` | 过程 | 190 |
| `(bitwise-arithmetic-shift-left *exint[1]* *exint[2]*)` | 过程 | 189 |
| `(bitwise-arithmetic-shift-right *exint[1]* *exint[2]*)` | 过程 | 189 |
| `(按位位计数 *exint*)` | 过程 | 187 |
| `(按位位字段 *exint[1]* *exint[2]* *exint[3]*)` | 过程 | 189 |
| `(按位位设置? *exint[1]* *exint[2]*)` | 过程 | 188 |
| `(按位复制位 *exint[1]* *exint[2]* *exint[3]*)` | 过程 | 188 |
| `(按位复制位字段 *exint[1]* *exint[2]* *exint[3]* *exint[4]*)` | 过程 | 189 |
| `(按位第一个位设置 *exint*)` | 过程 | 187 |
| `(按位条件 *exint[1]* *exint[2]* *exint[3]*)` | 过程 | 186 |
| `(按位或 *exint* ...)` | 过程 | 186 |
| `(按位长度 *exint*)` | 过程 | 187 |
| `(按位非 *exint*)` | 过程 | 186 |
| `(按位反转位字段 *exint[1]* *exint[2]* *exint[3]*)` | 过程 | 191 |
| `(按位旋转位字段 *exint[1]* *exint[2]* *exint[3]* *exint[4]*)` | 过程 | 190 |
| `(按位异或 *exint* ...)` | 过程 | 186 |
| `(布尔=? *boolean[1]* *boolean[2]*)` | 过程 | 243 |
| `(布尔? *obj*)` | 过程 | 150 |
| `(绑定标识符=? *identifier[1]* *identifier[2]*)` | 过程 | 302 |
| `(缓冲区模式 *symbol*)` | 语法 | 261 |
| `(缓冲区模式? *obj*)` | 语法 | 262 |
| `(字节向量->有符号整数列表 *bytevector* *eness* *size*)` | 过程 | 238 |
| `(字节向量->字符串 *bytevector* *transcoder*)` | 过程 | 286 |
| `(字节向量->u8 列表 *bytevector*)` | 过程 | 232 |
| `(字节向量->无符号整数列表 *bytevector* *eness* *size*)` | 过程 | 238 |
| `(字节向量复制 *bytevector*)` | 过程 | 229 |
| `(字节向量复制! *src* *src-start* *dst* *dst-start* *n*)` | 过程 | 230 |
| `(字节向量填充! *bytevector* *fill*)` | 过程 | 229 |
| `(字节向量 IEEE 双精度本机引用 *bytevector* *n*)` | 过程 | 239 |
| `(字节向量 IEEE 双精度本机设置! *bytevector* *n* *x*)` | 过程 | 239 |
| `(字节向量 IEEE 双精度引用 *bytevector* *n* *eness*)` | 过程 | 240 |
| `(字节向量 IEEE 双精度设置! *bytevector* *n* *x* *eness*)` | 过程 | 240 |
| `(字节向量 IEEE 单精度本机引用 *bytevector* *n*)` | 过程 | 239 |
| `(bytevector-ieee-single-native-set! *bytevector* *n* *x*)` | 过程 | 239 |
| `(bytevector-ieee-single-ref *bytevector* *n* *eness*)` | 过程 | 240 |
| `(bytevector-ieee-single-set! *bytevector* *n* *x* *eness*)` | 过程 | 240 |
| `(bytevector-length *bytevector*)` | 过程 | 229 |
| `(bytevector-s16-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-s16-native-set! *bytevector* *n* *s16*)` | 过程 | 233 |
| `(bytevector-s16-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-s16-set! *bytevector* *n* *s16* *eness*)` | 过程 | 236 |
| `(bytevector-s32-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-s32-native-set! *bytevector* *n* *s32*)` | 过程 | 233 |
| `(bytevector-s32-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-s32-set! *bytevector* *n* *s32* *eness*)` | 过程 | 236 |
| `(bytevector-s64-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-s64-native-set! *bytevector* *n* *s64*)` | 过程 | 233 |
| `(bytevector-s64-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-s64-set! *bytevector* *n* *s64* *eness*)` | 过程 | 236 |
| `(bytevector-s8-ref *bytevector* *n*)` | 过程 | 231 |
| `(bytevector-s8-set! *bytevector* *n* *s8*)` | 过程 | 231 |
| `(bytevector-sint-ref *bytevector* *n* *eness* *size*)` | 过程 | 237 |
| `(bytevector-sint-set! *bytevector* *n* *sint* *eness* *size*)` | 过程 | 238 |
| `(bytevector-u16-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-u16-native-set! *bytevector* *n* *u16*)` | 过程 | 233 |
| `(bytevector-u16-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-u16-set! *bytevector* *n* *u16* *eness*)` | 过程 | 236 |
| `(bytevector-u32-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-u32-native-set! *bytevector* *n* *u32*)` | 过程 | 233 |
| `(bytevector-u32-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-u32-set! *bytevector* *n* *u32* *eness*)` | 过程 | 236 |
| `(bytevector-u64-native-ref *bytevector* *n*)` | 过程 | 232 |
| `(bytevector-u64-native-set! *bytevector* *n* *u64*)` | 过程 | 233 |
| `(bytevector-u64-ref *bytevector* *n* *eness*)` | 过程 | 235 |
| `(bytevector-u64-set! *bytevector* *n* *u64* *eness*)` | 过程 | 236 |
| `(bytevector-u8-ref *bytevector* *n*)` | 过程 | 230 |
| `(bytevector-u8-set! *bytevector* *n* *u8*)` | 过程 | 231 |
| `(bytevector-uint-ref *bytevector* *n* *eness* *size*)` | 过程 | 237 |
| `(bytevector-uint-set! *bytevector* *n* *uint* *eness* *size*)` | 过程 | 238 |
| `(bytevector=? *bytevector[1]* *bytevector[2]*)` | 过程 | 229 |
| `(bytevector? *obj*)` | 过程 | 155 |
| `(caaaar *pair*)` | 过程 | 157 |
| `(caaadr *pair*)` | 过程 | 157 |
| `(caaar *pair*)` | 过程 | 157 |
| `(caadar *pair*)` | 过程 | 157 |
| `(caaddr *pair*)` | 过程 | 157 |
| `(caadr *pair*)` | 过程 | 157 |
| `(caar *pair*)` | 过程 | 157 |
| `(cadaar *pair*)` | 过程 | 157 |
| `(cadadr *pair*)` | 过程 | 157 |
| `(cadar *pair*)` | 过程 | 157 |
| `(caddar *pair*)` | 过程 | 157 |
| `(cadddr *pair*)` | 过程 | 157 |
| `(caddr *pair*)` | 过程 | 157 |
| `(cadr *pair*)` | 过程 | 157 |
| `(call-with-bytevector-output-port *procedure*)` | 过程 | 266 |
| `(call-with-bytevector-output-port *procedure* *?transcoder*)` | 过程 | 266 |
| `(call-with-current-continuation *procedure*)` | 过程 | 123 |
| `(call-with-input-file *path* *procedure*)` | 过程 | 281 |
| `(call-with-output-file *path* *procedure*)` | 过程 | 282 |
| `(call-with-port *port* *procedure*)` | 过程 | 272 |
| `(call-with-string-output-port *procedure*)` | 过程 | 267 |
| `(call-with-values *producer* *consumer*)` | 过程 | 131 |
| `(call/cc *procedure*)` | 过程 | 123 |
| `(car *pair*)` | 过程 | 156 |
| `(case *expr[0]* *clause[1]* *clause[2]* ...)` | 语法 | 113 |
| `(case-lambda *clause* ...)` | 语法 | 94 |
| `(cdaaar *pair*)` | 过程 | 157 |
| `(cdaadr *pair*)` | 过程 | 157 |
| `(cdaar *pair*)` | 过程 | 157 |
| `(cdadar *pair*)` | 过程 | 157 |
| `(cdaddr *pair*)` | 过程 | 157 |
| `(cdadr *pair*)` | 过程 | 157 |
| `(cdar *pair*)` | 过程 | 157 |
| `(cddaar *pair*)` | 过程 | 157 |
| `(cddadr *pair*)` | 过程 | 157 |
| `(cddar *pair*)` | 过程 | 157 |
| `(cdddar *pair*)` | 过程 | 157 |
| `(cddddr *pair*)` | 过程 | 157 |
| `(cdddr *pair*)` | 过程 | 157 |
| `(cddr *pair*)` | 过程 | 157 |
| `(cdr *pair*)` | 过程 | 156 |
| `(ceiling *real*)` | 过程 | 177 |
| `(char->integer *char*)` | 过程 | 215 |
| `(char-alphabetic? *char*)` | 过程 | 213 |
| `(char-ci<=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char-ci<? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char-ci=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char-ci>=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char-ci>? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char-downcase *char*)` | 过程 | 214 |
| `(char-foldcase *char*)` | 过程 | 215 |
| `(char-general-category *char*)` | 过程 | 214 |
| `(char-lower-case? *char*)` | 过程 | 213 |
| `(char-numeric? *char*)` | 过程 | 213 |
| `(char-title-case? *char*)` | 过程 | 213 |
| `(char-titlecase *char*)` | 过程 | 214 |
| `(char-upcase *char*)` | 过程 | 214 |
| `(char-upper-case? *char*)` | 过程 | 213 |
| `(char-whitespace? *char*)` | 过程 | 213 |
| `(char<=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char<? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char>=? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char>? *char[1]* *char[2]* *char[3]* ...)` | 过程 | 212 |
| `(char? *obj*)` | 过程 | 154 |
| `(close-input-port *input-port*)` | 过程 | 285 |
| `(close-output-port *output-port*)` | 过程 | 285 |
| `(close-port *port*)` | 过程 | 270 |
| `(command-line)` | 过程 | 350 |
| `(complex? *obj*)` | 过程 | 151 |
| `(cond *clause[1]* *clause[2]* ...)` | 语法 | 111 |
| `(condition *condition* ...)` | 过程 | 362 |
| `(condition-accessor *rtd* *procedure*)` | 过程 | 365 |
| `(condition-irritants *condition*)` | 过程 | 368 |
| `(condition-message *condition*)` | 过程 | 368 |
| `(condition-predicate *rtd*)` | 过程 | 365 |
| `(condition-who *condition*)` | 过程 | 369 |
| `(condition? *obj*)` | 过程 | 362 |
| `(cons *obj[1]* *obj[2]*)` | 过程 | 156 |
| `(cons* *obj* ... *final-obj*)` | 过程 | 158 |
| `*constant*` | 语法 | 141 |
| `(cos *num*)` | 过程 | 185 |
| `(current-error-port)` | 过程 | 263 |
| `(current-input-port)` | 过程 | 263 |
| `(current-output-port)` | 过程 | 263 |
| `(datum->syntax *template-identifier* *obj*)` | 过程 | 308 |
| `(define *var* *expr*)` | 语法 | 100 |
| `(define *var*)` | 语法 | 100 |
| `(define (*var[0]* *var[1]* ...) *body[1]* *body[2]* ...)` | 语法 | 100 |
| `(define (*var[0]* . *var[r]*) *body[1]* *body[2]* ...)` | 语法 | 100 |
| `(define (*var[0]* *var[1]* *var[2]* ... . *var[r]*) *body[1]* *body[2]* ...)` | 语法 | 100 |
| `(define-condition-type *name* *parent* *constructor* *pred* *field* ...)` | 语法 | 364 |
| `(define-enumeration *name* (*symbol* ...) *constructor*)` | 语法 | 250 |
| `(define-record-type *record-name* *clause* ...)` | 语法 | 328 |
| `(define-record-type (*record-name* *constructor* *pred*) *clause* ...)` | 语法 | 328 |
| `(define-syntax *keyword* *expr*)` | 语法 | 292 |
| `(delay *expr*)` | 语法 | 128 |
| `(delete-file *path*)` | 过程 | 286 |
| `(denominator *rat*)` | 过程 | 181 |
| `(display *obj*)` | 过程 | 285 |
| `(display *obj* *textual-output-port*)` | 过程 | 285 |
| `(div *x[1]* *x[2]*)` | 过程 | 175 |
| `(div-and-mod *x[1]* *x[2]*)` | 过程 | 175 |
| `(div0 *x[1]* *x[2]*)` | 过程 | 176 |
| `(div0-and-mod0 *x[1]* *x[2]*)` | 过程 | 176 |
| `(do ((*var* *init* *update*) ...) (*test* *result* ...) *expr* ...)` | 语法 | 115 |
| `(dynamic-wind *in* *body* *out*)` | 过程 | 124 |
| `else` | 语法 | 112 |
| `(endianness *symbol*)` | 语法 | 228 |
| `(enum-set->list *enum-set*)` | 过程 | 252 |
| `(enum-set-complement *enum-set*)` | 过程 | 254 |
| `(enum-set-constructor *enum-set*)` | 过程 | 251 |
| `(enum-set-difference *enum-set[1]* *enum-set[2]*)` | 过程 | 253 |
| `(enum-set-indexer *enum-set*)` | 过程 | 254 |
| `(enum-set-intersection *enum-set[1]* *enum-set[2]*)` | 过程 | 253 |
| `(enum-set-member? *symbol* *enum-set*)` | 过程 | 253 |
| `(enum-set-projection *enum-set[1]* *enum-set[2]*)` | 过程 | 254 |
| `(enum-set-subset? *enum-set[1]* *enum-set[2]*)` | 过程 | 252 |
| `(enum-set-union *enum-set[1]* *enum-set[2]*)` | 过程 | 253 |
| `(enum-set-universe *enum-set*)` | 过程 | 252 |
| `(enum-set=? *enum-set[1]* *enum-set[2]*)` | 过程 | 252 |
| `(environment *import-spec* ...)` | 过程 | 137 |
| `(eof-object)` | 过程 | 273 |
| `(eof-object? *obj*)` | 过程 | 273 |
| `(eol-style *symbol*)` | 语法 | 259 |
| `(eq? *obj[1]* *obj[2]*)` | 过程 | 143 |
| `(equal-hash *obj*)` | 过程 | 245 |
| `(equal? *obj[1]* *obj[2]*)` | 过程 | 148 |
| `(eqv? *obj[1]* *obj[2]*)` | 过程 | 146 |
| `(error *who* *msg* *irritant* ...)` | 过程 | 358 |
| `(error-handling-mode *symbol*)` | 语法 | 260 |
| `(error? *obj*)` | 过程 | 367 |
| `(eval *obj* *environment*)` | 过程 | 136 |
| `(even? *int*)` | 过程 | 174 |
| `(exact *num*)` | 过程 | 180 |
| `(exact->inexact *num*)` | 过程 | 181 |
| `(exact-integer-sqrt *n*)` | 过程 | 184 |
| `(exact? *num*)` | 过程 | 170 |
| `(exists *procedure* *list[1]* *list[2]* ...)` | 过程 | 119 |
| `(exit)` | 过程 | 350 |
| `(exit *obj*)` | 过程 | 350 |
| `(exp *num*)` | 过程 | 184 |
| `(expt *num[1]* *num[2]*)` | 过程 | 179 |
| `fields` | 语法 | 331 |
| `(file-exists? *path*)` | 过程 | 286 |
| `(file-options *symbol* ...)` | 语法 | 261 |
| `(filter *procedure* *list*)` | 过程 | 164 |
| `(find *procedure* *list*)` | 过程 | 165 |
| `(finite? *real*)` | 过程 | 174 |
| `(fixnum->flonum *fx*)` | 过程 | 211 |
| `(fixnum-width)` | 过程 | 193 |
| `(fixnum? *obj*)` | 过程 | 193 |
| `(fl* *fl* ...)` | 过程 | 207 |
| `(fl+ *fl* ...)` | 过程 | 206 |
| `(fl- *fl*)` | 过程 | 206 |
| `(fl- *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 206 |
| `(fl/ *fl*)` | 过程 | 207 |
| `(fl/ *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 207 |
| `(fl<=? *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 203 |
| `(fl<? *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 203 |
| `(fl=? *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 203 |
| `(fl>=? *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 203 |
| `(fl>? *fl[1]* *fl[2]* *fl[3]* ...)` | 过程 | 203 |
| `(flabs *fl*)` | 过程 | 209 |
| `(flacos *fl*)` | 过程 | 210 |
| `(flasin *fl*)` | 过程 | 210 |
| `(flatan *fl*)` | 过程 | 210 |
| `(flatan *fl[1]* *fl[2]*)` | 过程 | 210 |
| `(flceiling *fl*)` | 过程 | 208 |
| `(flcos *fl*)` | 过程 | 210 |
| `(fldenominator *fl*)` | 过程 | 209 |
| `(fldiv *fl[1]* *fl[2]*)` | 过程 | 207 |
| `(fldiv-and-mod *fl[1]* *fl[2]*)` | 过程 | 207 |
| `(fldiv0 *fl[1]* *fl[2]*)` | 过程 | 208 |
| `(fldiv0-and-mod0 *fl[1]* *fl[2]*)` | 过程 | 208 |
| `(fleven? *fl-int*)` | 过程 | 205 |
| `(flexp *fl*)` | 过程 | 209 |
| `(flexpt *fl[1]* *fl[2]*)` | 过程 | 210 |
| `(flfinite? *fl*)` | 过程 | 205 |
| `(flfloor *fl*)` | 过程 | 208 |
| `(flinfinite? *fl*)` | 过程 | 205 |
| `(flinteger? *fl*)` | 过程 | 204 |
| `(fllog *fl*)` | 过程 | 209 |
| `(fllog *fl[1]* *fl[2]*)` | 过程 | 209 |
| `(flmax *fl[1]* *fl[2]* ...)` | 过程 | 205 |
| `(flmin *fl[1]* *fl[2]* ...)` | 过程 | 205 |
| `(flmod *fl[1]* *fl[2]*)` | 过程 | 207 |
| `(flmod0 *fl[1]* *fl[2]*)` | 过程 | 208 |
| `(flnan? *fl*)` | 过程 | 205 |
| `(flnegative? *fl*)` | 过程 | 204 |
| `(flnumerator *fl*)` | 过程 | 209 |
| `(flodd? *fl-int*)` | 过程 | 205 |
| `(flonum? *obj*)` | 过程 | 203 |
| `(floor *real*)` | 过程 | 177 |
| `(flpositive? *fl*)` | 过程 | 204 |
| `(flround *fl*)` | 过程 | 208 |
| `(flsin *fl*)` | 过程 | 210 |
| `(flsqrt *fl*)` | 过程 | 210 |
| `(fltan *fl*)` | 过程 | 210 |
| `(fltruncate *fl*)` | 过程 | 208 |
| `(flush-output-port *output-port*)` | 过程 | 280 |
| `(flzero? *fl*)` | 过程 | 204 |
| `(fold-left *procedure* *obj* *list[1]* *list[2]* ...)` | 过程 | 120 |
| `(fold-right *procedure* *obj* *list[1]* *list[2]* ...)` | 过程 | 121 |
| `(for-all *procedure* *list[1]* *list[2]* ...)` | 过程 | 119 |
| `(for-each *procedure* *list[1]* *list[2]* ...)` | 过程 | 118 |
| `(force *promise*)` | 过程 | 128 |
| `(free-identifier=? *identifier[1]* *identifier[2]*)` | 过程 | 302 |
| `(fx* *fx[1]* *fx[2]*)` | 过程 | 195 |
| `(fx*/carry *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [197](https://objects.html#./objects:s162) |
| `(fx+ *fx[1]* *fx[2]*)` | 过程 | [195](https://objects.html#./objects:s157) |
| `(fx+/carry *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [197](https://objects.html#./objects:s162) |
| `(fx- *fx*)` | 过程 | [195](https://objects.html#./objects:s158) |
| `(fx- *fx[1]* *fx[2]*)` | 过程 | [195](https://objects.html#./objects:s158) |
| `(fx-/carry *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [197](https://objects.html#./objects:s162) |
| `(fx<=? *fx[1]* *fx[2]* *fx[3]* ...)` | 过程 | [193](https://objects.html#./objects:s153) |
| `(fx<? *fx[1]* *fx[2]* *fx[3]* ...)` | 过程 | [193](https://objects.html#./objects:s153) |
| `(fx=? *fx[1]* *fx[2]* *fx[3]* ...)` | 过程 | [193](https://objects.html#./objects:s153) |
| `(fx>=? *fx[1]* *fx[2]* *fx[3]* ...)` | 过程 | [193](https://objects.html#./objects:s153) |
| `(fx>? *fx[1]* *fx[2]* *fx[3]* ...)` | 过程 | [193](https://objects.html#./objects:s153) |
| `(fxand *fx* ...)` | 过程 | [197](https://objects.html#./objects:s163) |
| `(fxarithmetic-shift *fx[1]* *fx[2]*)` | 过程 | [201](https://objects.html#./objects:s173) |
| `(fxarithmetic-shift-left *fx[1]* *fx[2]*)` | 过程 | [201](https://objects.html#./objects:s172) |
| `(fxarithmetic-shift-right *fx[1]* *fx[2]*)` | 过程 | [201](https://objects.html#./objects:s172) |
| `(fxbit-count *fx*)` | 过程 | [198](https://objects.html#./objects:s165) |
| `(fxbit-field *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [200](https://objects.html#./objects:s170) |
| `(fxbit-set? *fx[1]* *fx[2]*)` | 过程 | [199](https://objects.html#./objects:s168) |
| `(fxcopy-bit *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [200](https://objects.html#./objects:s169) |
| `(fxcopy-bit-field *fx[1]* *fx[2]* *fx[3]* *fx[4]*)` | 过程 | [200](https://objects.html#./objects:s171) |
| `(fxdiv *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s160) |
| `(fxdiv-and-mod *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s160) |
| `(fxdiv0 *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s161) |
| `(fxdiv0-and-mod0 *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s161) |
| `(fxeven? *fx*)` | 过程 | [194](https://objects.html#./objects:s155) |
| `(fxfirst-bit-set *fx*)` | 过程 | [199](https://objects.html#./objects:s167) |
| `(fxif *fx[1]* *fx[2]* *fx[3]*)` | 过程 | [198](https://objects.html#./objects:s164) |
| `(fxior *fx* ...)` | 过程 | [197](https://objects.html#./objects:s163) |
| `(fxlength *fx*)` | 过程 | [198](https://objects.html#./objects:s166) |
| `(fxmax *fx[1]* *fx[2]* ...)` | 过程 | [195](https://objects.html#./objects:s156) |
| `(fxmin *fx[1]* *fx[2]* ...)` | 过程 | [195](https://objects.html#./objects:s156) |
| `(fxmod *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s160) |
| `(fxmod0 *fx[1]* *fx[2]*)` | 过程 | [196](https://objects.html#./objects:s161) |
| `(fxnegative? *fx*)` | 过程 | [194](https://objects.html#./objects:s154) |
| `(fxnot *fx*)` | 过程 | [197](https://objects.html#./objects:s163) |
| `(fxodd? *fx*)` | 过程 | [194](https://objects.html#./objects:s155) |
| `(fxpositive? *fx*)` | 过程 | 194 |
| `(fxreverse-bit-field *fx[1]* *fx[2]* *fx[3]*)` | 过程 | 202 |
| `(fxrotate-bit-field *fx[1]* *fx[2]* *fx[3]* *fx[4]*)` | 过程 | 201 |
| `(fxxor *fx* ...)` | 过程 | 197 |
| `(fxzero? *fx*)` | 过程 | 194 |
| `(gcd *int* ...)` | 过程 | 179 |
| `(generate-temporaries *list*)` | 过程 | 310 |
| `(get-bytevector-all *binary-input-port*)` | 过程 | 275 |
| `(get-bytevector-n *binary-input-port* *n*)` | 过程 | 274 |
| `(get-bytevector-n! *binary-input-port* *bytevector* *start* *n*)` | 过程 | 274 |
| `(get-bytevector-some *binary-input-port*)` | 过程 | 275 |
| `(get-char *textual-input-port*)` | 过程 | 275 |
| `(get-datum *textual-input-port*)` | 过程 | 278 |
| `(get-line *textual-input-port*)` | 过程 | 277 |
| `(get-string-all *textual-input-port*)` | 过程 | 277 |
| `(get-string-n *textual-input-port* *n*)` | 过程 | 276 |
| `(get-string-n! *textual-input-port* *string* *start* *n*)` | 过程 | 276 |
| `(get-u8 *binary-input-port*)` | 过程 | 274 |
| `(greatest-fixnum)` | 过程 | 193 |
| `(guard (*var* *clause[1]* *clause[2]* ...) *b1* *b2* ...)` | 语法 | 361 |
| `(hashtable-clear! *hashtable*)` | 过程 | 249 |
| `(hashtable-clear! *hashtable* *size*)` | 过程 | 249 |
| `(hashtable-contains? *hashtable* *key*)` | 过程 | 246 |
| `(hashtable-copy *hashtable*)` | 过程 | 248 |
| `(hashtable-copy *hashtable* *mutable?*)` | 过程 | 248 |
| `(hashtable-delete! *hashtable* *key*)` | 过程 | 248 |
| `(hashtable-entries *hashtable*)` | 过程 | 250 |
| `(hashtable-equivalence-function *hashtable*)` | 过程 | 245 |
| `(hashtable-hash-function *hashtable*)` | 过程 | 245 |
| `(hashtable-keys *hashtable*)` | 过程 | 249 |
| `(hashtable-mutable? *hashtable*)` | 过程 | 245 |
| `(hashtable-ref *hashtable* *key* *default*)` | 过程 | 246 |
| `(hashtable-set! *hashtable* *key* *obj*)` | 过程 | 246 |
| `(hashtable-size *hashtable*)` | 过程 | 248 |
| `(hashtable-update! *hashtable* *key* *procedure* *default*)` | 过程 | 247 |
| `(hashtable? *obj*)` | 过程 | 155 |
| `(i/o-decoding-error? *obj*)` | 过程 | 375 |
| `(i/o-encoding-error-char *condition*)` | 过程 | 376 |
| `(i/o-encoding-error? *obj*)` | 过程 | 376 |
| `(i/o-error-filename *condition*)` | 过程 | 373 |
| `(i/o-error-port *condition*)` | 过程 | 375 |
| `(i/o-error-position *condition*)` | 过程 | 372 |
| `(i/o-error? *obj*)` | 过程 | 371 |
| `(i/o-file-already-exists-error? *obj*)` | 过程 | 374 |
| `(i/o-file-does-not-exist-error? *obj*)` | 过程 | 374 |
| `(i/o-file-is-read-only-error? *obj*)` | 过程 | 374 |
| `(i/o-file-protection-error? *obj*)` | 过程 | 373 |
| `(i/o-filename-error? *obj*)` | 过程 | 373 |
| `(i/o-invalid-position-error? *obj*)` | 过程 | 372 |
| `(i/o-port-error? *obj*)` | 过程 | 375 |
| `(i/o-read-error? *obj*)` | 过程 | 372 |
| `(i/o-write-error? *obj*)` | 过程 | 372 |
| `(identifier-syntax *tmpl*)` | 语法 | 297 |
| `(identifier-syntax (*id[1]* *tmpl[1]*) ((set! *id[2]* *e[2]*) *tmpl[2]*))` | 语法 | 297 |
| `(identifier? *obj*)` | 过程 | 301 |
| `(if *test* *consequent* *alternative*)` | 语法 | 109 |
| `(if *test* *consequent*)` | 语法 | 109 |
| `(imag-part *num*)` | 过程 | 182 |
| `immutable` | 语法 | 331 |
| `(implementation-restriction-violation? *obj*)` | 过程 | 369 |
| `(inexact *num*)` | 过程 | 180 |
| `(inexact->exact *num*)` | 过程 | 181 |
| `(inexact? *num*)` | 过程 | 170 |
| `(infinite? *real*)` | 过程 | 174 |
| `(input-port? *obj*)` | 过程 | 270 |
| `(integer->char *n*)` | 过程 | 215 |
| `(integer-valued? *obj*)` | 过程 | 153 |
| `(integer? *obj*)` | 过程 | 151 |
| `(irritants-condition? *obj*)` | 过程 | 368 |
| `(lambda *formals* *body[1]* *body[2]* ...)` | 语法 | 92 |
| `(latin-1-codec)` | 过程 | 259 |
| `(lcm *int* ...)` | 过程 | 179 |
| `(least-fixnum)` | 过程 | 193 |
| `(length *list*)` | 过程 | 159 |
| `(let ((*var* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 95 |
| `(let *name* ((*var* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 114 |
| `(let* ((*var* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 96 |
| `(let*-values ((*formals* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 99 |
| `(let-syntax ((*keyword* *expr*) ...) *form[1]* *form[2]* ...)` | 语法 | 293 |
| `(let-values ((*formals* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 99 |
| `(letrec ((*var* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 97 |
| `(letrec* ((*var* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 98 |
| `(letrec-syntax ((*keyword* *expr*) ...) *form[1]* *form[2]* ...)` | 语法 | 293 |
| `(lexical-violation? *obj*)` | 过程 | 370 |
| `(list *obj* ...)` | 过程 | 158 |
| `(list->string *list*)` | 过程 | 223 |
| `(list->vector *list*)` | 过程 | 226 |
| `(list-ref *list* *n*)` | 过程 | 159 |
| `(list-sort *predicate* *list*)` | 过程 | 167 |
| `(list-tail *list* *n*)` | 过程 | 160 |
| `(list? *obj*)` | 过程 | 158 |
| `(log *num*)` | 过程 | 184 |
| `(log *num[1]* *num[2]*)` | 过程 | 184 |
| `(lookahead-char *textual-input-port*)` | 过程 | 275 |
| `(lookahead-u8 *binary-input-port*)` | 过程 | 274 |
| `(magnitude *num*)` | 过程 | 183 |
| `(make-assertion-violation)` | 过程 | 366 |
| `(make-bytevector *n*)` | 过程 | 228 |
| `(make-bytevector *n* *fill*)` | 过程 | 228 |
| `(make-custom-binary-input-port *id* *r!* *gp* *sp!* *close*)` | 过程 | 267 |
| `(make-custom-binary-input/output-port *id* *r!* *w!* *gp* *sp!* *close*)` | 过程 | 267 |
| `(make-custom-binary-output-port *id* *w!* *gp* *sp!* *close*)` | 过程 | 267 |
| `(make-custom-textual-input-port *id* *r!* *gp* *sp!* *close*)` | 过程 | 268 |
| `(make-custom-textual-input/output-port *id* *r!* *w!* *gp* *sp!* *close*)` | 过程 | 268 |
| `(make-custom-textual-output-port *id* *w!* *gp* *sp!* *close*)` | 过程 | 268 |
| `(make-enumeration *symbol-list*)` | 过程 | 251 |
| `(make-eq-hashtable)` | 过程 | 243 |
| `(make-eq-hashtable *size*)` | 过程 | 243 |
| `(make-eqv-hashtable)` | 过程 | 244 |
| `(make-eqv-hashtable *size*)` | 过程 | 244 |
| `(make-error)` | 过程 | 367 |
| `(make-hashtable *hash* *equiv?*)` | 过程 | 244 |
| `(make-hashtable *hash* *equiv?* *size*)` | 过程 | 244 |
| `(make-i/o-decoding-error *pobj*)` | 过程 | 375 |
| `(make-i/o-encoding-error *pobj* *cobj*)` | 过程 | 376 |
| `(make-i/o-error)` | 过程 | 371 |
| `(make-i/o-file-already-exists-error *filename*)` | 过程 | 374 |
| `(make-i/o-file-does-not-exist-error *filename*)` | 过程 | 374 |
| `(make-i/o-file-is-read-only-error *filename*)` | 过程 | 374 |
| `(make-i/o-file-protection-error *filename*)` | 过程 | 373 |
| `(make-i/o-filename-error *filename*)` | 过程 | 373 |
| `(make-i/o-invalid-position-error *position*)` | 过程 | 372 |
| `(make-i/o-port-error *pobj*)` | 过程 | 375 |
| `(make-i/o-read-error)` | 过程 | 372 |
| `(make-i/o-write-error)` | 过程 | 372 |
| `(make-implementation-restriction-violation)` | 过程 | 369 |
| `(make-irritants-condition *irritants*)` | 过程 | 368 |
| `(make-lexical-violation)` | 过程 | 370 |
| `(make-message-condition *message*)` | 过程 | 368 |
| `(make-no-infinities-violation)` | 过程 | 376 |
| `(make-no-nans-violation)` | 过程 | 377 |
| `(make-non-continuable-violation)` | 过程 | 369 |
| `(make-polar *real[1]* *real[2]*)` | 过程 | 183 |
| `(make-record-constructor-descriptor *rtd* *parent-rcd* *protocol*)` | 过程 | 332 |
| `(make-record-type-descriptor *name* *parent* *uid* *s?* *o?* *fields*)` | 过程 | 331 |
| `(make-rectangular *real[1]* *real[2]*)` | 过程 | 182 |
| `(make-serious-condition)` | 过程 | 366 |
| `(make-string *n*)` | 过程 | 218 |
| `(make-string *n* *char*)` | 过程 | 218 |
| `(make-syntax-violation *form* *subform*)` | 过程 | 370 |
| `(make-transcoder *codec*)` | 过程 | 259 |
| `(make-transcoder *codec* *eol-style*)` | 过程 | 259 |
| `(make-transcoder *codec* *eol-style* *error-handling-mode*)` | 过程 | 259 |
| `(make-undefined-violation)` | 过程 | 371 |
| `(make-variable-transformer *procedure*)` | 过程 | 306 |
| `(make-vector *n*)` | 过程 | 224 |
| `(make-vector *n* *obj*)` | 过程 | 224 |
| `(make-violation)` | 过程 | 366 |
| `(make-warning)` | 过程 | 367 |
| `(make-who-condition *who*)` | 过程 | 369 |
| `(map *procedure* *list[1]* *list[2]* ...)` | 过程 | 117 |
| `(max *real[1]* *real[2]* ...)` | 过程 | 178 |
| `(member *obj* *list*)` | 过程 | 161 |
| `(memp *procedure* *list*)` | 过程 | 163 |
| `(memq *obj* *list*)` | 过程 | 161 |
| `(memv *obj* *list*)` | 过程 | 161 |
| `(message-condition? *obj*)` | 过程 | 368 |
| `(min *real[1]* *real[2]* ...)` | 过程 | 178 |
| `(mod *x[1]* *x[2]*)` | 过程 | 175 |
| `(mod0 *x[1]* *x[2]*)` | 过程 | 176 |
| `(modulo *int[1]* *int[2]*)` | 过程 | 175 |
| `mutable` | 语法 | 331 |
| `(nan? *real*)` | 过程 | 174 |
| `(本地字节顺序)` | 过程 | 228 |
| `(本地换行风格)` | 过程 | 260 |
| `(本地转码器)` | 过程 | 259 |
| `(negative? *real*)` | 过程 | 173 |
| `(newline)` | 过程 | 285 |
| `(newline *textual-output-port*)` | 过程 | 285 |
| `(no-infinities-violation? *obj*)` | 过程 | 376 |
| `(no-nans-violation? *obj*)` | 过程 | 377 |
| `(non-continuable-violation? *obj*)` | 过程 | 369 |
| `nongenerative` | 语法 | 331 |
| `(not *obj*)` | 过程 | 110 |
| `(null-environment *version*)` | 过程 | 137 |
| `(null? *obj*)` | 过程 | 151 |
| `(number->string *num*)` | 过程 | 191 |
| `(number->string *num* *radix*)` | 过程 | 191 |
| `(number->string *num* *radix* *precision*)` | 过程 | 191 |
| `(number? *obj*)` | 过程 | 151 |
| `(numerator *rat*)` | 过程 | 181 |
| `(odd? *int*)` | 过程 | 174 |
| `opaque` | 语法 | 331 |
| `(open-bytevector-input-port *bytevector*)` | 过程 | 264 |
| `(open-bytevector-input-port *bytevector* *?transcoder*)` | 过程 | 264 |
| `(open-bytevector-output-port)` | 过程 | 265 |
| `(open-bytevector-output-port *?transcoder*)` | 过程 | 265 |
| `(open-file-input-port *path*)` | 过程 | 262 |
| `(open-file-input-port *path* *options*)` | 过程 | 262 |
| `(open-file-input-port *path* *options* *b-mode*)` | 过程 | 262 |
| `(open-file-input-port *path* *options* *b-mode* *?transcoder*)` | 过程 | 262 |
| `(open-file-input/output-port *path*)` | 过程 | 263 |
| `(open-file-input/output-port *path* *options*)` | 过程 | 263 |
| `(open-file-input/output-port *path* *options* *b-mode*)` | 过程 | 263 |
| `(open-file-input/output-port *path* *options* *b-mode* *?transcoder*)` | 过程 | 263 |
| `(open-file-output-port *path*)` | 过程 | 262 |
| `(open-file-output-port *path* *options*)` | 过程 | 262 |
| `(open-file-output-port *path* *options* *b-mode*)` | 过程 | 262 |
| `(open-file-output-port *path* *options* *b-mode* *?transcoder*)` | 过程 | 262 |
| `(open-input-file *path*)` | 过程 | 280 |
| `(open-output-file *path*)` | 过程 | 281 |
| `(open-string-input-port *string*)` | 过程 | 265 |
| `(open-string-output-port)` | 过程 | 266 |
| `(or *expr* ...)` | 语法 | 110 |
| `(output-port-buffer-mode *port*)` | 过��� | 273 |
| `(output-port? *obj*)` | 过程 | 270 |
| `(pair? *obj*)` | 过程 | 151 |
| `parent` | 语法 | 331 |
| `parent-rtd` | 语法 | 331 |
| `(partition *procedure* *list*)` | 过程 | 164 |
| `(peek-char)` | 过程 | 284 |
| `(peek-char *textual-input-port*)` | 过程 | 284 |
| `(port-eof? *input-port*)` | 过程 | 278 |
| `(port-has-port-position? *port*)` | 过程 | 271 |
| `(port-has-set-port-position!? *port*)` | 过程 | 272 |
| `(port-position *port*)` | 过程 | 271 |
| `(port-transcoder *port*)` | 过程 | 271 |
| `(port? *obj*)` | 过程 | 270 |
| `(positive? *real*)` | 过程 | 173 |
| `(*expr[0]* *expr[1]* ...)` | 语法 | 107 |
| `(procedure? *obj*)` | 过程 | 155 |
| `protocol` | 语法 | 331 |
| `(put-bytevector *binary-output-port* *bytevector*)` | 过程 | 279 |
| `(put-bytevector *binary-output-port* *bytevector* *start*)` | 过程 | 279 |
| `(put-bytevector *binary-output-port* *bytevector* *start* *n*)` | 过程 | 279 |
| `(put-char *textual-output-port* *char*)` | 过程 | 279 |
| `(put-datum *textual-output-port* *obj*)` | 过程 | 279 |
| `(put-string *textual-output-port* *string*)` | 过程 | 279 |
| `(put-string *textual-output-port* *string* *start*)` | 过程 | 279 |
| `(put-string *textual-output-port* *string* *start* *n*)` | 过程 | 279 |
| `(put-u8 *binary-output-port* *octet*)` | 过程 | 278 |
| `(quasiquote *obj* ...)` | 语法 | 142 |
| `(quasisyntax *template* ...)` | 语法 | 305 |
| `(quote *obj*)` | 语法 | 141 |
| `(quotient *int[1]* *int[2]*)` | 过程 | 175 |
| `(raise *obj*)` | 过程 | 357 |
| `(raise-continuable *obj*)` | 过程 | 357 |
| `(rational-valued? *obj*)` | 过程 | 153 |
| `(rational? *obj*)` | 过程 | 151 |
| `(rationalize *real[1]* *real[2]*)` | 过程 | 181 |
| `(read)` | 过程 | 284 |
| `(read *textual-input-port*)` | 过程 | 284 |
| `(read-char)` | 过程 | 284 |
| `(read-char *textual-input-port*)` | 过程 | 284 |
| `(real->flonum *real*)` | 过程 | 211 |
| `(real-part *num*)` | 过程 | 182 |
| `(real-valued? *obj*)` | 过程 | 153 |
| `(real? *obj*)` | 过程 | 151 |
| `(record-accessor *rtd* *idx*)` | 过程 | 334 |
| `(record-constructor *rcd*)` | 过程 | 333 |
| `(record-constructor-descriptor *record-name*)` | 语法 | 333 |
| `(record-field-mutable? *rtd* *idx*)` | 过程 | 338 |
| `(record-mutator *rtd* *idx*)` | 过程 | 334 |
| `(record-predicate *rtd*)` | 过程 | 333 |
| `(record-rtd *record*)` | 过程 | 338 |
| `(record-type-descriptor *record-name*)` | 语法 | 333 |
| `(record-type-descriptor? *obj*)` | 过程 | 332 |
| `(record-type-field-names *rtd*)` | 过程 | 337 |
| `(record-type-generative? *rtd*)` | 过程 | 337 |
| `(record-type-name *rtd*)` | 过程 | 336 |
| `(record-type-opaque? *rtd*)` | 过程 | 337 |
| `(record-type-parent *rtd*)` | 过程 | 336 |
| `(record-type-sealed? *rtd*)` | 过程 | 337 |
| `(record-type-uid *rtd*)` | 过程 | 336 |
| `(record? *obj*)` | 过程 | 338 |
| `(remainder *int[1]* *int[2]*)` | 过程 | 175 |
| `(remove *obj* *list*)` | 过程 | 163 |
| `(remp *procedure* *list*)` | 过程 | 163 |
| `(remq *obj* *list*)` | 过程 | 163 |
| `(remv *obj* *list*)` | 过程 | 163 |
| `(reverse *list*)` | 过程 | 161 |
| `(round *real*)` | 过程 | 178 |
| `(scheme-report-environment *version*)` | 过程 | 137 |
| `sealed` | 语法 | 331 |
| `(serious-condition? *obj*)` | 过程 | 366 |
| `(set! *var* *expr*)` | 语法 | 102 |
| `(set-car! *pair* *obj*)` | 过程 | 157 |
| `(set-cdr! *pair* *obj*)` | 过程 | 157 |
| `(set-port-position! *port* *pos*)` | 过程 | 272 |
| `(simple-conditions *condition*)` | 过程 | 363 |
| `(sin *num*)` | 过程 | 185 |
| `(sint-list->bytevector *list* *eness* *size*)` | 过程 | 239 |
| `(sqrt *num*)` | 过程 | 183 |
| `(standard-error-port)` | 过程 | 264 |
| `(standard-input-port)` | 过程 | 264 |
| `(standard-output-port)` | 过程 | 264 |
| `(string *char* ...)` | 过程 | 218 |
| `(string->bytevector *string* *transcoder*)` | 过程 | 287 |
| `(string->list *string*)` | 过程 | 222 |
| `(string->number *string*)` | 过程 | 191 |
| `(string->number *string* *radix*)` | 过程 | 191 |
| `(string->symbol *string*)` | 过程 | 242 |
| `(string->utf16 *string*)` | 过程 | 287 |
| `(string->utf16 *string* *endianness*)` | 过程 | 287 |
| `(string->utf32 *string*)` | 过程 | 287 |
| `(string->utf32 *string* *endianness*)` | 过程 | 287 |
| `(string->utf8 *string*)` | 过程 | 287 |
| `(string-append *string* ...)` | 过程 | 219 |
| `(string-ci-hash *string*)` | 过程 | 245 |
| `(string-ci<=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 217 |
| `(string-ci<? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 217 |
| `(string-ci=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 217 |
| `(string-ci>=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 217 |
| `(string-ci>? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 217 |
| `(string-copy *string*)` | 过程 | 219 |
| `(string-downcase *string*)` | 过程 | 221 |
| `(string-fill! *string* *char*)` | 过程 | 220 |
| `(string-foldcase *string*)` | 过程 | 221 |
| `(string-for-each *procedure* *string[1]* *string[2]* ...)` | 过程 | 122 |
| `(string-hash *string*)` | 过程 | 245 |
| `(string-length *string*)` | 过程 | 218 |
| `(string-normalize-nfc *string*)` | 过程 | 222 |
| `(string-normalize-nfd *string*)` | 过程 | 222 |
| `(string-normalize-nfkc *string*)` | 过程 | 222 |
| `(string-normalize-nfkd *string*)` | 过程 | 222 |
| `(string-ref *string* *n*)` | 过程 | 218 |
| `(string-set! *string* *n* *char*)` | 过程 | 219 |
| `(string-titlecase *string*)` | 过程 | 221 |
| `(string-upcase *string*)` | 过程 | 221 |
| `(string<=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 216 |
| `(string<? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 216 |
| `(string=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 216 |
| `(string>=? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 216 |
| `(string>? *string[1]* *string[2]* *string[3]* ...)` | 过程 | 216 |
| `(string? *obj*)` | 过程 | 154 |
| `(substring *string* *start* *end*)` | 过程 | 220 |
| `(symbol->string *symbol*)` | 过程 | 242 |
| `(symbol-hash *symbol*)` | 过程 | 245 |
| `(symbol=? *symbol[1]* *symbol[2]*)` | 过程 | 242 |
| `(symbol? *obj*)` | 过程 | 154 |
| `(syntax *template*)` | 语法 | 300 |
| `(syntax->datum *obj*)` | 过程 | 308 |
| `(syntax-case *expr* (*literal* ...) *clause* ...)` | 语法 | 299 |
| `(syntax-rules (*literal* ...) *clause* ...)` | 语法 | 294 |
| `(syntax-violation *who* *msg* *form*)` | 过程 | 359 |
| `(syntax-violation *who* *msg* *form* *subform*)` | 过程 | 359 |
| `(syntax-violation-form *condition*)` | 过程 | 370 |
| `(syntax-violation-subform *condition*)` | 过程 | 370 |
| `(syntax-violation? *obj*)` | 过程 | 370 |
| `(tan *num*)` | 过程 | 185 |
| `(textual-port? *obj*)` | 过程 | 270 |
| `(transcoded-port *binary-port* *transcoder*)` | 过程 | 271 |
| `(transcoder-codec *transcoder*)` | 过程 | 259 |
| `(transcoder-eol-style *transcoder*)` | 过程 | 259 |
| `(transcoder-error-handling-mode *transcoder*)` | 过程 | 259 |
| `(truncate *real*)` | 过程 | 177 |
| `(u8-list->bytevector *list*)` | 过程 | 232 |
| `(uint-list->bytevector *list* *eness* *size*)` | 过程 | 239 |
| `(undefined-violation? *obj*)` | 过程 | 371 |
| `(unless *test-expr* *expr[1]* *expr[2]* ...)` | 语法 | 112 |
| `(unquote *obj* ...)` | 语法 | 142 |
| `(unquote-splicing *obj* ...)` | 语法 | 142 |
| `(unsyntax *template* ...)` | 语法 | 305 |
| `(unsyntax-splicing *template* ...)` | 语法 | 305 |
| `(utf-16-codec)` | 过程 | 259 |
| `(utf-8-codec)` | 过程 | 259 |
| `(utf16->string *bytevector* *endianness*)` | 过程 | 288 |
| `(utf16->string *bytevector* *endianness* *endianness-mandatory?*)` | 过程 | 288 |
| `(utf32->string *bytevector* *endianness*)` | 过程 | 288 |
| `(utf32->string *bytevector* *endianness* *endianness-mandatory?*)` | 过程 | 288 |
| `(utf8->string *bytevector*)` | 过程 | 287 |
| `(values *obj* ...)` | 过程 | 131 |
| `*variable*` | 语法 | 91 |
| `(vector *obj* ...)` | 过程 | 224 |
| `(vector->list *vector*)` | 过程 | 225 |
| `(vector-fill! *vector* *obj*)` | 过程 | 225 |
| `(vector-for-each *procedure* *vector[1]* *vector[2]* ...)` | 过程 | 122 |
| `(vector-length *vector*)` | 过程 | 224 |
| `(vector-map *procedure* *vector[1]* *vector[1]* ...)` | 过程 | 121 |
| `(vector-ref *vector* *n*)` | 过程 | 224 |
| `(vector-set! *vector* *n* *obj*)` | 过程 | 225 |
| `(vector-sort *predicate* *vector*)` | 过程 | 226 |
| `(vector-sort! *predicate* *vector*)` | 过程 | 226 |
| `(vector? *obj*)` | 过程 | 154 |
| `(violation? *obj*)` | 过程 | 366 |
| `(warning? *obj*)` | 过程 | 367 |
| `(when *test-expr* *expr[1]* *expr[2]* ...)` | 语法 | 112 |
| `(who-condition? *obj*)` | 过程 | 369 |
| `(with-exception-handler *procedure* *thunk*)` | 过程 | 360 |
| `(with-input-from-file *path* *thunk*)` | 过程 | 283 |
| `(with-output-to-file *path* *thunk*)` | 过程 | 283 |
| `(with-syntax ((*pattern* *expr*) ...) *body[1]* *body[2]* ...)` | 语法 | 304 |
| `(write *obj*)` | 过程 | 284 |
| `(write *obj* *textual-output-port*)` | 过程 | 284 |
| `(write-char *char*)` | 过程 | 285 |
| `(write-char *char* *textual-output-port*)` | 过程 | 285 |
| `(zero? *num*)` | 过程 | 173 |
