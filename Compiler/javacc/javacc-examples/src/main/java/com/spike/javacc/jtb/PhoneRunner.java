//package com.spike.javacc.jtb;
//
//import com.spike.javacc.jtb.phone.ParseException;
//import com.spike.javacc.jtb.phone.PhoneParser;
//import com.spike.javacc.jtb.phone.syntaxtree.PhoneList;
//import com.spike.javacc.jtb.phone.visitor.SchemeTreeBuilder;
//import com.spike.javacc.jtb.phone.visitor.TreeDumper;
//
//import java.io.StringReader;
//
//public class PhoneRunner {
//    public static void main(String[] args) {
//        StringReader sr = new StringReader("432-789-9876 123-456-7890 888-555-1212");
//        PhoneParser p = new PhoneParser(sr);
//        try {
//            PhoneList pl = p.PhoneList();
//            // 432-789-9876 123-456-7890 888-555-1212
//            pl.accept(new TreeDumper());
//            System.out.println();
//            // (define root '(PhoneList ((PhoneNumber "432" "-" "789" "-" "9876" ) (PhoneNumber "123" "-" "456" "-" "7890" ) (PhoneNumber "888" "-" "555" "-" "1212" ) ) ))
//            pl.accept(new SchemeTreeBuilder());
//        } catch (ParseException e) {
//            e.printStackTrace();
//        }
//    }
//}
