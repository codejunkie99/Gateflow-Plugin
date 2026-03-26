module tb_axi4lite_slave;
    logic clk=0, rst_n=0;
    logic [7:0] awaddr, araddr;
    logic awvalid=0, wvalid=0, bready=1, arvalid=0, rready=1;
    logic awready, wready, bvalid, arready, rvalid;
    logic [31:0] wdata, rdata;
    logic [3:0] wstrb;
    logic [1:0] bresp, rresp;
    int pass_count=0, fail_count=0;

    axi4lite_slave #(.ADDR_WIDTH(8), .DATA_WIDTH(32), .NUM_REGS(4)) u_dut (.*);
    always #5 clk = ~clk;

    task axi_write(input logic [7:0] addr, input logic [31:0] data);
        @(posedge clk);
        awaddr = addr; awvalid = 1; wdata = data; wstrb = 4'hF; wvalid = 1;
        @(posedge clk); awvalid = 0; wvalid = 0;
        wait(bvalid); @(posedge clk);
    endtask

    task axi_read(input logic [7:0] addr, output logic [31:0] data);
        @(posedge clk);
        araddr = addr; arvalid = 1;
        @(posedge clk); arvalid = 0;
        wait(rvalid); data = rdata; @(posedge clk);
    endtask

    initial begin
        logic [31:0] rd;
        $dumpfile("dump.vcd"); $dumpvars(0, tb_axi4lite_slave);
        repeat(3) @(posedge clk); rst_n = 1; @(posedge clk);
        axi_write(8'h00, 32'hDEADBEEF);
        axi_read(8'h00, rd);
        if (rd === 32'hDEADBEEF) begin $display("PASS: read-after-write"); pass_count++; end
        else begin $display("FAIL: got %08h", rd); fail_count++; end
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
