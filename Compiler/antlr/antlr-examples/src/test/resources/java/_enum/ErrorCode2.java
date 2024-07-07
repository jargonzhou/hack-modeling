package com._enum;

public enum ErrorCode2 {
    ERROR_CODE_1("ERROR_CODE_1", "ERROR_MSG_1", "ERROR_MSG_1ZH"),
    ERROR_CODE_2("ERROR_CODE_2", "ERROR_MSG_2", "ERROR_MSG_2ZH");

    private String code;
    private String msgEN;
    private String msgZH;

    ErrorCode2(String code, String msgEN, String msgZH) {
        this.code = code;
        this.msgEN = msgEN;
        this.msgZH = msgZH;
    }
}