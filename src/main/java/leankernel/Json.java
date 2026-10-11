package leankernel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Minimal JSON reader: objects -> Map, arrays -> List, numbers -> Long (or Double), strings, booleans, null. */
public final class Json {
    private final String s;
    private int p;

    private Json(String s) { this.s = s; }

    public static Object parse(String text) {
        Json j = new Json(text);
        j.ws();
        Object v = j.value();
        j.ws();
        if (j.p != text.length()) throw new IllegalArgumentException("trailing JSON at " + j.p);
        return v;
    }

    private void ws() { while (p < s.length() && s.charAt(p) <= ' ') p++; }

    private Object value() {
        char c = s.charAt(p);
        switch (c) {
            case '{': return object();
            case '[': return array();
            case '"': return string();
            case 't': p += 4; return Boolean.TRUE;
            case 'f': p += 5; return Boolean.FALSE;
            case 'n': p += 4; return null;
            default: return number();
        }
    }

    private Map<String, Object> object() {
        Map<String, Object> m = new LinkedHashMap<>();
        p++;
        ws();
        if (s.charAt(p) == '}') { p++; return m; }
        while (true) {
            ws();
            String k = string();
            ws();
            if (s.charAt(p++) != ':') throw new IllegalArgumentException("expected ':' at " + p);
            ws();
            m.put(k, value());
            ws();
            char c = s.charAt(p++);
            if (c == '}') return m;
            if (c != ',') throw new IllegalArgumentException("expected ',' at " + p);
        }
    }

    private List<Object> array() {
        List<Object> l = new ArrayList<>();
        p++;
        ws();
        if (s.charAt(p) == ']') { p++; return l; }
        while (true) {
            ws();
            l.add(value());
            ws();
            char c = s.charAt(p++);
            if (c == ']') return l;
            if (c != ',') throw new IllegalArgumentException("expected ',' at " + p);
        }
    }

    private String string() {
        if (s.charAt(p++) != '"') throw new IllegalArgumentException("expected string at " + p);
        StringBuilder sb = new StringBuilder();
        while (true) {
            char c = s.charAt(p++);
            if (c == '"') return sb.toString();
            if (c != '\\') { sb.append(c); continue; }
            char e = s.charAt(p++);
            switch (e) {
                case 'n': sb.append('\n'); break;
                case 't': sb.append('\t'); break;
                case 'r': sb.append('\r'); break;
                case 'b': sb.append('\b'); break;
                case 'f': sb.append('\f'); break;
                case 'u': sb.append((char) Integer.parseInt(s.substring(p, p + 4), 16)); p += 4; break;
                default: sb.append(e);
            }
        }
    }

    private Object number() {
        int st = p;
        while (p < s.length() && "+-0123456789.eE".indexOf(s.charAt(p)) >= 0) p++;
        String t = s.substring(st, p);
        if (t.isEmpty()) throw new IllegalArgumentException("bad JSON at " + st);
        if (t.indexOf('.') >= 0 || t.indexOf('e') >= 0 || t.indexOf('E') >= 0) return Double.parseDouble(t);
        return Long.parseLong(t);
    }
}
