package com._enum;

public enum ErrorCode1 {
    ERROR_CODE_1("ERROR_CODE_1", "ERROR_MSG_1"),
    ERROR_CODE_2("ERROR_CODE_2", "ERROR_MSG_2"),
    ;

    private String code;
    private String msg;

    ErrorCode1(String code, String msg) {
        this.code = code;
        this.msg = msg;
    }
}