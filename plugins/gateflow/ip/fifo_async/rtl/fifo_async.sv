module fifo_async #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 8
) (
    input  logic             wr_clk,
    input  logic             wr_rst_n,
    input  logic             wr_en,
    input  logic [WIDTH-1:0] wr_data,
    output logic             full,
    input  logic             rd_clk,
    input  logic             rd_rst_n,
    input  logic             rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic             empty
);
    localparam int ADDR_W = $clog2(DEPTH);
    logic [WIDTH-1:0] mem [DEPTH];
    logic [ADDR_W:0] wr_ptr, rd_ptr;
    logic [ADDR_W:0] wr_ptr_gray, rd_ptr_gray;
    logic [ADDR_W:0] wr_ptr_gray_sync, rd_ptr_gray_sync;

    // Gray code conversion
    function automatic logic [ADDR_W:0] bin2gray(input logic [ADDR_W:0] bin);
        return bin ^ (bin >> 1);
    endfunction

    assign wr_ptr_gray = bin2gray(wr_ptr);
    assign rd_ptr_gray = bin2gray(rd_ptr);

    // Synchronizers
    logic [ADDR_W:0] wr_sync [2], rd_sync [2];
    always_ff @(posedge rd_clk or negedge rd_rst_n)
        if (!rd_rst_n) begin rd_sync[0] <= '0; rd_sync[1] <= '0; end
        else begin rd_sync[0] <= wr_ptr_gray; rd_sync[1] <= rd_sync[0]; end
    assign wr_ptr_gray_sync = rd_sync[1];

    always_ff @(posedge wr_clk or negedge wr_rst_n)
        if (!wr_rst_n) begin wr_sync[0] <= '0; wr_sync[1] <= '0; end
        else begin wr_sync[0] <= rd_ptr_gray; wr_sync[1] <= wr_sync[0]; end
    assign rd_ptr_gray_sync = wr_sync[1];

    // Full/empty
    assign full  = (wr_ptr_gray == {~rd_ptr_gray_sync[ADDR_W:ADDR_W-1], rd_ptr_gray_sync[ADDR_W-2:0]});
    assign empty = (rd_ptr_gray == wr_ptr_gray_sync);

    // Write
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) wr_ptr <= '0;
        else if (wr_en && !full) begin
            mem[wr_ptr[ADDR_W-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1'b1;
        end
    end

    // Read
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) rd_ptr <= '0;
        else if (rd_en && !empty) rd_ptr <= rd_ptr + 1'b1;
    end
    assign rd_data = mem[rd_ptr[ADDR_W-1:0]];
endmodule
