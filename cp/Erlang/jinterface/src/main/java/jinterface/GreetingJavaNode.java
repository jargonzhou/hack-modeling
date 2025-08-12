package jinterface;

import java.io.IOException;

import com.ericsson.otp.erlang.OtpErlangObject;
import com.ericsson.otp.erlang.OtpErlangPid;
import com.ericsson.otp.erlang.OtpErlangString;
import com.ericsson.otp.erlang.OtpErlangTuple;
import com.ericsson.otp.erlang.OtpMbox;
import com.ericsson.otp.erlang.OtpNode;

/**
 * <pre>
 * 运行
 * 
 * 先启动Erlang节点以启动EMPD:
 * $ erl -sname erlangNode -setcookie secret
 * 
 * (erlangNode@zhoujiagen)4> net_adm:ping('javaNode@zhoujiagen').
 * pong
 * 
 * % 使用邮箱和节点传递消息
 * (erlangNode@zhoujiagen)5> {theMailbox, javaNode@zhoujiagen} ! {self(), "Bob"}.
 * {<0.63.0>,"Bob"}
 * (erlangNode@zhoujiagen)6> receive {MBox, Msg} -> Msg end.
 * "Greeting from Java, Bob!"
 * (erlangNode@zhoujiagen)7> MBox.
 * <7568.1.0>
 * (erlangNode@zhoujiagen)8> MBox ! {self(), "Cartman"}.   % 直接使用邮箱传递消息
 * {<0.63.0>,"Cartman"}
 * (erlangNode@zhoujiagen)9> receive Reply -> Reply end.
 * {<7568.1.0>,"Greeting from Java, Cartman!"}
 * 
 * 
 * </pre>
 * 
 * @author zhoujiagen
 */
public class GreetingJavaNode {

	private OtpNode node;
	private OtpMbox mbox;

	public GreetingJavaNode(String nodeName, String mboxName, String cookie)
			throws IOException {
		node = new OtpNode(nodeName, cookie);
		mbox = node.createMbox(mboxName); // 具名邮箱
	}

	public static void main(String[] args) throws IOException {
		String nodeName = "javaNode";
		String mboxName = "theMailbox";
		String cookie = "secret";
		GreetingJavaNode javaNode = //
		new GreetingJavaNode(nodeName, mboxName, cookie);

		// 启动节点
		javaNode.start();
	}

	/**
	 * <pre>
	 * 启动节点
	 * 
	 * 接收消息格式: {SenderPid, "[Bob]"}
	 * 回复消息格式: {MboxPid, "Greeting from Java, [Bob]!"}
	 * </pre>
	 */
	public void start() {
		while (true) {
			try {

				OtpErlangObject msg = mbox.receive(); // 阻塞等待消息

				// 消息处理
				OtpErlangTuple t = (OtpErlangTuple) msg;
				OtpErlangPid senderPid = (OtpErlangPid) t.elementAt(0);
				String name = ((OtpErlangString) t.elementAt(1)).stringValue();

				// 回复消息
				String greeting = "Greeting from Java, " + name + "!";
				OtpErlangString replyContent = new OtpErlangString(greeting);
				OtpErlangTuple replyMsg = new OtpErlangTuple(//
						new OtpErlangObject[] { mbox.self(), replyContent });
				mbox.send(senderPid, replyMsg);

			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}
}
