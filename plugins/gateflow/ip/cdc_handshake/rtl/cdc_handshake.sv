module cdc_handshake #(
    parameter int WIDTH = 8
) (
    input  logic             src_clk,
    input  logic             src_rst_n,
    input  logic [WIDTH-1:0] src_data,
    input  logic             src_valid,
    output logic             src_ready,
    input  logic             dst_clk,
    input  logic             dst_rst_n,
    output logic [WIDTH-1:0] dst_data,
    output logic             dst_valid
);
    logic req_src, ack_src;
    logic [1:0] req_sync, ack_sync;
    logic [WIDTH-1:0] data_hold;

    // Source domain
    always_ff @(posedge src_clk or negedge src_rst_n) begin
        if (!src_rst_n) begin
            req_src   <= 1'b0;
            data_hold <= '0;
            ack_sync  <= '0;
        end else begin
            ack_sync <= {ack_sync[0], ack_src};
            if (src_valid && src_ready) begin
                data_hold <= src_data;
                req_src   <= !req_src;
            end
        end
    end
    assign src_ready = (req_src == ack_sync[1]);

    // Destination domain
    logic req_dst_prev;
    always_ff @(posedge dst_clk or negedge dst_rst_n) begin
        if (!dst_rst_n) begin
            req_sync     <= '0;
            ack_src      <= 1'b0;
            req_dst_prev <= 1'b0;
            dst_valid    <= 1'b0;
            dst_data     <= '0;
        end else begin
            req_sync     <= {req_sync[0], req_src};
            req_dst_prev <= req_sync[1];
            dst_valid    <= 1'b0;
            if (req_sync[1] != req_dst_prev) begin
                dst_data  <= data_hold;
                dst_valid <= 1'b1;
                ack_src   <= req_sync[1];
            end
        end
    end
endmodule
