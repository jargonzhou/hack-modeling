package com.spike.javacc.examples.apache_log;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.Reader;
import java.util.Comparator;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

public class AgentCollector {
    private Map<String, Integer> userAgentCount = new TreeMap<>();

    private File file;

    public AgentCollector(File file) {
        this.file = file;
    }

    public void addUserAgentHit(String image) {
        if (!userAgentCount.containsKey(image)) {
            userAgentCount.put(image, 1);
            return;
        }
        userAgentCount.put(image, userAgentCount.get(image) + 1);
    }

    public void collect() throws FileNotFoundException, ParseException {
        Reader r = new FileReader(file);
        ApacheLog p = new ApacheLog(r);
        p.setAgentCollector(this);
        p.Log();
        System.out.println("Skipped lines: " + p.getSkipLines());
    }

    public void printReport() {
        TreeSet<Map.Entry<String, Integer>> sorted = new TreeSet<Map.Entry<String, Integer>>(new Comparator<Map.Entry<String, Integer>>() {
            @Override
            public int compare(Map.Entry<String, Integer> o1, Map.Entry<String, Integer> o2) {
                return o2.getValue().compareTo(o1.getValue());
            }
        });
        sorted.addAll(userAgentCount.entrySet());
        for (Map.Entry<String, Integer> entry : sorted) {
            if (entry.getValue() < 10) {
                break;
            }
            System.out.println(entry.getValue() + " hits from " + entry.getKey());
        }
    }

    public static void main(String[] args) throws Exception {
        // https://github.com/elastic/examples/blob/master/Common%20Data%20Formats/apache_logs/apache_logs
        AgentCollector collector = new AgentCollector(new File("src/main/resources/apache.log"));
        collector.collect();
        collector.printReport();
    }

    // Output:
//Skipped lines: [8899]
//1044 hits from "Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/32.0.1700.107 Safari/537.36"
//369 hits from "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_9_1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/33.0.1750.91 Safari/537.36"
// ...
}
