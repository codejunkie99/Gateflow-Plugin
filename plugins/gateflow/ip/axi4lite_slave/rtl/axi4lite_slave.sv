module axi4lite_slave #(
    parameter int ADDR_WIDTH = 8,
    parameter int DATA_WIDTH = 32,
    parameter int NUM_REGS   = 16
) (
    input  logic                    clk,
    input  logic                    rst_n,
    // Write address
    input  logic [ADDR_WIDTH-1:0]   awaddr,
    input  logic                    awvalid,
    output logic                    awready,
    // Write data
    input  logic [DATA_WIDTH-1:0]   wdata,
    input  logic [DATA_WIDTH/8-1:0] wstrb,
    input  logic                    wvalid,
    output logic                    wready,
    // Write response
    output logic [1:0]              bresp,
    output logic                    bvalid,
    input  logic                    bready,
    // Read address
    input  logic [ADDR_WIDTH-1:0]   araddr,
    input  logic                    arvalid,
    output logic                    arready,
    // Read data
    output logic [DATA_WIDTH-1:0]   rdata,
    output logic [1:0]              rresp,
    output logic                    rvalid,
    input  logic                    rready
);
    logic [DATA_WIDTH-1:0] regs [NUM_REGS];
    localparam int REG_ADDR_W = $clog2(NUM_REGS);

    // Write path
    assign awready = !bvalid || bready;
    assign wready  = awready;
    assign bresp   = 2'b00;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bvalid <= 1'b0;
            for (int i = 0; i < NUM_REGS; i++) regs[i] <= '0;
        end else begin
            if (bvalid && bready) bvalid <= 1'b0;
            if (awvalid && awready && wvalid && wready) begin
                for (int b = 0; b < DATA_WIDTH/8; b++)
                    if (wstrb[b])
                        regs[awaddr[REG_ADDR_W+1:2]][b*8 +: 8] <= wdata[b*8 +: 8];
                bvalid <= 1'b1;
            end
        end
    end

    // Read path
    assign arready = !rvalid || rready;
    assign rresp   = 2'b00;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rvalid <= 1'b0;
            rdata  <= '0;
        end else begin
            if (rvalid && rready) rvalid <= 1'b0;
            if (arvalid && arready) begin
                rdata  <= regs[araddr[REG_ADDR_W+1:2]];
                rvalid <= 1'b1;
            end
        end
    end
endmodule
